-- Prove2me | Theorems.Thm_SamplingAC0_lemma_12
-- name    : SamplingAC0.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:48:40.579746+00:00
-- url     : https://prove2.me/theorems/3ccaada4-88b8-4f38-bd2e-caabf31084da
-- title:
--   Lemma 12 — a restriction that keeps the conflict
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $q=2^k$ with $k\ge1$, $d=q^{1/10}$ and $\delta=q^{-3}$, fix an encoding of $\mathbb F_q$ by $k$ bits, and let $f=(h,g)$ be a forest of depth at most $d$ on $s$ input bits with the $b$ output positions of $R$; $h_\ell$ is its tree at the line position $\ell$, and $g_i$ is the $i$-th point decoded from its point-list outputs. If
--
--   $$\Delta(f(U),R)\le\delta,$$
--
--   then there are a restriction $\rho$ and an index $i\in[q]$ such that
--
--   1. (C1) $f|_\rho$ is average-$q^{5/4}$-Lipschitz;
--   2. (C2) $\mathbb P[f(U)\text{ is invalid}\mid\rho]\le c\,\delta$;
--   3. (C3) $\mathbb P[h_\ell(U)=0\mid\rho]\ge0.01$, for a uniformly random line $\ell$ independent of $U$;
--   4. (C4) $\Delta\bigl((g_i(U)\mid\rho),U_{\mathbb F_q^2}\bigr)\le c\,q^{-1/16}$.
--
--   Probabilities given $\rho$ are over $U$ uniform among the inputs extending $\rho$. The restriction makes the forest Lipschitz while keeping the output almost always valid, a line bit $0$ with constant probability, and one listed point close to uniform.
--
--   The lemma is a step of a proof by contradiction: by Theorem 10, for large $q$ no forest satisfies its hypothesis, exactly as in the source.
--
--   **Formalization Note** One constant $c$ serves (C2) and (C4) and is chosen before the encoding, $k$, $s$ and $f$.
--
--   Differences from the source:
--   - reading: the standing assumptions of the proof of Theorem 10 ("For a large enough q"; (2), p.9) → the lemma for every q = 2^k ≥ 2, with no threshold on q; reason: the printed lemma states no threshold; this is the stronger reading
--   - encoding: ℓ ∼ L in (C3); U_{F_q²}; "| ρ" → average over the uniform line of P_{U | ρ}[h_ℓ(U) = 0]; the uniform distribution on F_q × F_q; U uniform among inputs extending ρ; one c before all objects; reason: same instances
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Lemma 12, p.10 (proof §3.2, pp.11–12; setting (2), p.9)

import Mathlib
import Definitions.Def_SamplingAC0_Forest
import Definitions.Def_SamplingAC0_law
import Definitions.Def_SamplingAC0_tvDist
import Definitions.Def_SamplingAC0_Restriction
import Definitions.Def_SamplingAC0_AvgLipschitz
import Definitions.Def_SamplingAC0_lineDNF
import Definitions.Def_SamplingAC0_R
set_option autoImplicit false

namespace SamplingAC0

/-- **Lemma 12 (a restriction preserving the conflict).** Riazanov–Viola, *Sampling Tools and the
Power of AC0*, STOC 2027 submission (manuscript sha256 99c33d30…), Lemma 12, p.10 (proof pp.11–12),
in the setting of (2), p.9 (`d := q^{1/10}`, `δ := q^{−3}`, `f` a forest `{0,1}^s → {0,1}^b` of
depth `≤ d`): "Suppose ∆(f(U), R) ≤ δ, and ℓ ∼ L. Then there exists a restriction ρ and an index
i ∈ [q] such that (C1) f|ρ is average-q^{5/4}-Lipschitz. (C2) P[f(U) is invalid | ρ] ≤ cδ.
(C3) P[h_ℓ(U) = 0 | ρ] ≥ 0.01. (C4) ∆((g_i(U) | ρ), U_{F_q²}) ≤ cq^{−1/16}."

Here `h_ℓ` is the tree of `f` at the line position `ℓ` and `g_i` is the `i`-th point decoded from
the point-list outputs of `f`. In (C3) the line `ℓ` is uniform and independent of `U`, which is
uniform among the inputs extending `ρ`.

**Formalization Note.** One absolute constant `c` serves (C2) and (C4) and comes before the encoding,
`k`, `s` and `f`. The statement is for every `q = 2^k ≥ 2`. -/
theorem lemma_12 : ∃ c : ℝ, 0 < c ∧ ∀ (enc : Encoding) (k : ℕ), 1 ≤ k →
    ∀ (s : ℕ) (f : Forest s (ROut k)), f.DepthLE (((2 : ℝ) ^ k) ^ ((1 : ℝ) / 10)) →
    tvDist (law f.eval) (R enc k) ≤ ((2 : ℝ) ^ k) ^ (-3 : ℝ) →
    ∃ (ρ : Restriction s) (i : Fin (2 ^ k)),
      AvgLipschitz f ρ (((2 : ℝ) ^ k) ^ ((5 : ℝ) / 4)) ∧
      pr (condRestr ρ) {x | Invalid enc (f.eval x)} ≤ c * ((2 : ℝ) ^ k) ^ (-3 : ℝ) ∧
      expect (PMF.uniformOfFintype (Line k))
          (fun ℓ => pr (condRestr ρ) {x | (f (Sum.inl ℓ)).eval x = false}) ≥ 0.01 ∧
      tvDist ((condRestr ρ).map (fun x => decodeOut enc (f.eval x) i))
          (PMF.uniformOfFintype (F k × F k)) ≤ c * ((2 : ℝ) ^ k) ^ (-(1 : ℝ) / 16) := by sorry

end SamplingAC0
