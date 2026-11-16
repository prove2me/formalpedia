-- Prove2me | Theorems.Thm_PottsRapidMixing_Supplement_theorem_1_2
-- name    : PottsRapidMixing.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:28:45.307622+00:00
-- url     : https://prove2.me/theorems/370f64f0-b2e8-4759-befc-ac742dd3119d
-- title:
--   Theorem 1.2, p.3 — Potts Glauber dynamics on boxes and tori of $\mathbb Z^d$ below $\beta_c$ has inverse gap $n^{1+o(1)}$ and mixing time $n^{2+o(1)}$
-- statement:
--   Fix integers $d\ge2$ and $q\ge2$, and let $0<\beta<\beta_c(q,\mathbb Z^d)$. Let $G$ be either the box $\{1,\dots,m\}^d$ with free boundary or the torus $(\mathbb Z/m\mathbb Z)^d$, so that $G$ has $n=m^d$ vertices. Let $\mu$ be the $q$-state Potts law at inverse temperature $\beta$ on $G$, $P$ its heat-bath Glauber dynamics, $\mathcal E(f,f)=\langle (I-P)f,f\rangle_\mu$ the Dirichlet form, and $d(t)=\max_\sigma\|P^t(\sigma,\cdot)-\mu\|_{\mathrm{TV}}$. Then the inverse spectral gap of $P$ is $n^{1+o(1)}$ and the mixing time is at most $n^{2+o(1)}$: for every $\varepsilon>0$ there is $M_0$ such that for every $m\ge M_0$, on both graphs,
--
--   1. $\operatorname{Var}_\mu(f)\le n^{1+\varepsilon}\,\mathcal E(f,f)$ for every $f:[q]^V\to\mathbb R$;
--   2. there is $f$ with $\operatorname{Var}_\mu(f)>0$ and $n^{1-\varepsilon}\,\mathcal E(f,f)\le\operatorname{Var}_\mu(f)$;
--   3. $$d\bigl(\lfloor n^{2+\varepsilon}\rfloor\bigr)\le\tfrac14 .$$
--
--   Items 1 and 2 say $n^{1-\varepsilon}\le \mathrm{gap}(P)^{-1}\le n^{1+\varepsilon}$, where $\mathrm{gap}(P)=\inf\{\mathcal E(f,f)/\operatorname{Var}_\mu(f):\operatorname{Var}_\mu(f)>0\}$. This is the lattice companion of the mission's goal: it extends rapid mixing of Potts Glauber dynamics on $\mathbb Z^d$ to the whole high-temperature regime, which goes beyond tree uniqueness, including $q\ge3$ in dimensions $d\ge3$, where strong spatial mixing up to $\beta_c$ is not known.
--
--   **Formalization Note** The threshold $\beta_c(q,\mathbb Z^d)$ is the supplement's `betaC`, the standard wired random-cluster definition, compared in `EReal`. The torus is the published `MarkovMixing.torusGraph d m`; its vertex type is finite only for $m\neq0$, so the torus clause carries an instance `NeZero m`, which costs nothing because $M_0$ can be taken positive. The variance, Dirichlet form, Glauber chain and $d(t)$ are the published `distVar`, `dirichlet`, `glauber` and `distStationary`.
--
--   Differences from the source:
--   - encoding: a cube in ℤ^d on n vertices → boxGraph d m on Fin d → Fin m (free boundary), n = m^d, statement for all m ≥ M₀; reason: §7 p.45 and Remark 7.3 p.48 prove it for the side-length m box {1,…,m}^d with free boundary, and n^{o(1)} is an asymptotic statement in n = m^d
--   - encoding: the d-dimensional torus graph on n vertices → MarkovMixing.torusGraph d m with an instance NeZero m, n = m^d; reason: the paper's (ℤ/mℤ)^d (§7, p.45); NeZero only makes the vertex type finite and excludes no large m
--   - reading: inverse spectral gap n^{1+o(1)} → for every ε > 0 eventually in m, the Poincaré inequality Var ≤ n^{1+ε} ℰ for all f and some f with Var > 0 and n^{1−ε} ℰ ≤ Var; reason: n^{1+o(1)} is two-sided; the gap is in its variational form, which is 1 − λ₂ for the reversible Glauber chain
--   - encoding: mixing time at most n^{2+o(1)} → d(⌊n^{2+ε}⌋) ≤ 1/4 for every ε > 0 eventually in m, with d = distStationary; reason: d(t) is nonincreasing, so this says t_mix ≤ ⌊n^{2+ε}⌋; it avoids the junk value of a natural-number sInf (paper.md R3)
--   - encoding: β_c(q, ℤ^d), used but not defined in the paper → betaC q d, the EReal supremum of the β > 0 with θ_N(1 − e^{−β}) → 0 for the wired box crossing probabilities θ_N; reason: the standard definition of the critical point through the random-cluster model, as the paper uses it in (7.1); equal to the infinite-volume critical point
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Theorem 1.2, p.3 (proved in §7, pp.45–48, Remark 7.3)

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_mm_mcmc
import Definitions.Def_mm_coupling
import Definitions.Def_LogSobolevMC_ChiSquare_Setting
import Definitions.Def_PottsRapidMixing_PottsLaw
import Definitions.Def_PottsRapidMixing_Supplement_Lattice

open scoped Classical
open Filter Topology

namespace PottsRapidMixing.Supplement

/-- **Theorem 1.2** (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.3). Fix integers `d ≥ 2`,
`q ≥ 2` and `0 < β < β_c(q, ℤ^d)`. The Potts Glauber dynamics on a cube in `ℤ^d` on `n` vertices has
inverse spectral gap `n^{1+o(1)}` and therefore mixing time at most `n^{2+o(1)}`. The same holds for the
`d`-dimensional torus graph on `n` vertices.

Here, for every `ε > 0` and every `m` large enough, with `n = m^d`, `µ` the Potts law and `P` its
Glauber chain, on the box `{1, …, m}^d` (free boundary) and on the torus `(ℤ/mℤ)^d`:
1. `Var_µ(f) ≤ n^{1+ε} ℰ(f, f)` for every `f` (inverse gap at most `n^{1+ε}`);
2. some `f` has `Var_µ(f) > 0` and `n^{1−ε} ℰ(f, f) ≤ Var_µ(f)` (inverse gap at least `n^{1−ε}`);
3. `d(⌊n^{2+ε}⌋) ≤ 1/4` (mixing time at most `n^{2+ε}`).

**Formalization Note.** `n^{1+o(1)}` is read as two-sided, for every `ε > 0` eventually in `m`. The gap is
in its variational form `inf ℰ(f,f)/Var_µ(f)` over nonconstant `f`, with the published `dirichlet` and
`distVar`; no eigenvalue or infimum appears. `t_mix ≤ T` is `d(⌊T⌋) ≤ 1/4` with `d = distStationary`.
The torus is the published `MarkovMixing.torusGraph d m`, whose vertex type is finite for `m ≠ 0`. -/
theorem theorem_1_2 (d q : ℕ) (hd : 2 ≤ d) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (hβc : (β : EReal) < betaC q d) :
    ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m →
      -- the box `{1, …, m}^d` with free boundary
      ((∀ f : ((Fin d → Fin m) → Fin q) → ℝ,
          MarkovMixing.distVar (pottsLaw (boxGraph d m) β q) f
            ≤ ((m : ℝ) ^ d) ^ (1 + ε) *
              LogSobolevMC.ChiSquare.dirichlet (MarkovMixing.glauber (pottsLaw (boxGraph d m) β q))
                (pottsLaw (boxGraph d m) β q) f f) ∧
        (∃ f : ((Fin d → Fin m) → Fin q) → ℝ,
          0 < MarkovMixing.distVar (pottsLaw (boxGraph d m) β q) f ∧
            ((m : ℝ) ^ d) ^ (1 - ε) *
              LogSobolevMC.ChiSquare.dirichlet (MarkovMixing.glauber (pottsLaw (boxGraph d m) β q))
                (pottsLaw (boxGraph d m) β q) f f
              ≤ MarkovMixing.distVar (pottsLaw (boxGraph d m) β q) f) ∧
        MarkovMixing.distStationary (MarkovMixing.glauber (pottsLaw (boxGraph d m) β q))
          (pottsLaw (boxGraph d m) β q) ⌊((m : ℝ) ^ d) ^ (2 + ε)⌋₊ ≤ 1 / 4) ∧
      -- the torus `(ℤ/mℤ)^d`
      (∀ [NeZero m],
        (∀ f : ((Fin d → ZMod m) → Fin q) → ℝ,
          MarkovMixing.distVar (pottsLaw (MarkovMixing.torusGraph d m) β q) f
            ≤ ((m : ℝ) ^ d) ^ (1 + ε) *
              LogSobolevMC.ChiSquare.dirichlet
                (MarkovMixing.glauber (pottsLaw (MarkovMixing.torusGraph d m) β q))
                (pottsLaw (MarkovMixing.torusGraph d m) β q) f f) ∧
        (∃ f : ((Fin d → ZMod m) → Fin q) → ℝ,
          0 < MarkovMixing.distVar (pottsLaw (MarkovMixing.torusGraph d m) β q) f ∧
            ((m : ℝ) ^ d) ^ (1 - ε) *
              LogSobolevMC.ChiSquare.dirichlet
                (MarkovMixing.glauber (pottsLaw (MarkovMixing.torusGraph d m) β q))
                (pottsLaw (MarkovMixing.torusGraph d m) β q) f f
              ≤ MarkovMixing.distVar (pottsLaw (MarkovMixing.torusGraph d m) β q) f) ∧
        MarkovMixing.distStationary
          (MarkovMixing.glauber (pottsLaw (MarkovMixing.torusGraph d m) β q))
          (pottsLaw (MarkovMixing.torusGraph d m) β q) ⌊((m : ℝ) ^ d) ^ (2 + ε)⌋₊ ≤ 1 / 4) := by sorry

end PottsRapidMixing.Supplement
