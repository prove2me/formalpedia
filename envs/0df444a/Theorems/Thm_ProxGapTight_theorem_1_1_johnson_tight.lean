-- Prove2me | Theorems.Thm_ProxGapTight_theorem_1_1_johnson_tight
-- name    : ProxGapTight.theorem_1_1_johnson_tight
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T07:52:40.787179+00:00
-- url     : https://prove2.me/theorems/c5fafcac-5208-4000-94f9-2cc251556ab5
-- title:
--   Theorem 1.1 — the one-and-a-half Johnson bound is tight for proximity gaps of linear codes
-- statement:
--   For every prime $p$, every $0<\delta<1$, every $\rho$ with
--   $$
--   J_{3/2}(\delta)=1-(1-\delta)^{1/3}<\rho<\Gamma(\delta)=1-(1-\delta)^{4/9},
--   $$
--   and every $\eta>0$, there are constants $A,c>0$, an integer $D\ge1$, an integer $s_0\ge1$ and a constant $K$, all depending only on $p,\delta,\rho,\eta$, with the following property. For every $s\ge s_0$, with $q=p^s$, and every block length $N$ with
--   $$
--   A s^D\le N<q,
--   $$
--   there are a nonzero linear code $C\subseteq\mathbb F_q^N$ and vectors $f,g\in\mathbb F_q^N$ such that
--
--   1. **Code parameters.** $|\delta(C)-\delta|<\eta$ and $|R(C)-(1-\delta(C))|\le K/s$;
--   2. **Distance of the defining vectors.** $\delta(f,C)>\Gamma(\delta)$ and $\delta(g,C)>\Gamma(\delta)$;
--   3. **Exceptional coefficients.** $|\mathcal Z_\rho(f,g;C)|\ge cq$.
--
--   So $C$ fails the proximity-gaps property at radius $\rho$, for every slack below $\Gamma(\delta)-\rho$ and every error bound below $c$. Since every linear code of relative distance $\delta$ has the property below $J_{3/2}(\delta)$ [BGKS20], the one-and-a-half Johnson radius is the exact threshold for general linear codes; for $\delta<3-\sqrt5$ the failures occur inside the unique-decoding radius $\delta/2$, disproving the Diamond–Gruen conjecture.
--
--   **Formalization Note** $\mathbb F_q$ is any field with $p^s$ elements; the term $O_{p,\delta,\rho,\eta}(1/s)$ is the bound $K/s$ with $K$ chosen before $s$.
--
--   Differences from the source:
--   - generalization: q := p^s and C ⊆ F_q^N → any field F with Fintype.card F = p ^ s; reason: all fields of order p^s are isomorphic to F_q; the statement specializes to F_q
--   - encoding: R(C) = 1 − δ(C) + O_{p,δ,ρ,η}(1/s) → ∃ K, chosen with A, c, D, s₀ before s, F, N, with |rate C − (1 − relDist C)| ≤ K / s; reason: the subscript lists exactly the allowed dependencies; '= … + O(·)' bounds the error in absolute value
--   - encoding: δ(C) for the code the theorem produces → C ≠ ⊥ added to the conclusion; reason: δ(C) presupposes a nonzero code; in Lean minDist ⊥ = 0 by the sInf ∅ = 0 convention
--   - encoding: coordinates [N]; minima over codewords → Fin N; natural-number sInf divided by N in ℝ; reason: the same values
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), Theorem 1.1, p.3 (restated as Theorem 3.1, pp.6–7; proof pp.12–15)

import Mathlib
import Definitions.Def_ProxGapTight_relDist
import Definitions.Def_ProxGapTight_rate
import Definitions.Def_ProxGapTight_distToCode
import Definitions.Def_ProxGapTight_exceptionalSet
import Definitions.Def_ProxGapTight_J32
import Definitions.Def_ProxGapTight_Gam

namespace ProxGapTight

/-- **Theorem 1.1** (restated as Theorem 3.1, pp.6–7; proved pp.12–15), Kominers, Thaler, Zheng,
*The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes*, manuscript
(Sept. 2026), p.3.

For every prime `p`, every `0 < δ < 1`, every `ρ ∈ (J_{3/2}(δ), Γ(δ))` and every `η > 0` there are
constants `A, c > 0`, an integer `D ≥ 1`, an integer `s₀ ≥ 1` (and the constant `K` of the
`O_{p,δ,ρ,η}(1/s)` term), depending only on `p, δ, ρ, η`, such that for every `s ≥ s₀`, with
`q = p^s`, and every block length `A s^D ≤ N < q`, there are a linear code `C ⊆ F_q^N` and
`f, g ∈ F_q^N` with `|δ(C) − δ| < η`, `|R(C) − (1 − δ(C))| ≤ K/s`, `δ(f, C), δ(g, C) > Γ(δ)` and
`|𝒵_ρ(f, g; C)| ≥ cq`.

**Formalization Note.** `F_q` is any field `F` with `Fintype.card F = p ^ s` (all are isomorphic to
`F_q`); coordinates are `Fin N`; "linear" is `F`-linear (`Submodule F (Fin N → F)`). The
`O_{p,δ,ρ,η}(1/s)` term is pinned as `∃ K` chosen with `A, c, D, s₀` before `s`, `F`, `N`, and
bounded in absolute value. `C ≠ ⊥` is part of the conclusion because `δ(C)` presupposes a nonzero
code. -/
theorem theorem_1_1_johnson_tight :
    ∀ p : ℕ, p.Prime → ∀ δ ρ η : ℝ, 0 < δ → δ < 1 → J32 δ < ρ → ρ < Gam δ → 0 < η →
      ∃ A c K : ℝ, 0 < A ∧ 0 < c ∧ ∃ D s₀ : ℕ, 1 ≤ D ∧ 1 ≤ s₀ ∧
        ∀ s : ℕ, s₀ ≤ s → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
          Fintype.card F = p ^ s →
          ∀ N : ℕ, A * (s : ℝ) ^ D ≤ (N : ℝ) → N < p ^ s →
            ∃ C : Submodule F (Fin N → F), ∃ f g : Fin N → F,
              C ≠ ⊥ ∧ |relDist C - δ| < η ∧ |rate C - (1 - relDist C)| ≤ K / (s : ℝ) ∧
              Gam δ < distToCode f C ∧ Gam δ < distToCode g C ∧
              c * ((p : ℝ) ^ s) ≤ ((exceptionalSet ρ f g C).card : ℝ) := by sorry

end ProxGapTight
