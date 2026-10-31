-- Prove2me | Theorems.Thm_ScarceIdeas_lemma_4
-- name    : ScarceIdeas.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:37.609982+00:00
-- url     : https://prove2.me/theorems/7f0bca1d-a228-4fc4-970d-01330eb1f155
-- title:
--   Lemma 4 [Single-crossing property]: at a crossing $p=p_{na}$, $p'_{na}<p'$
-- statement:
--   Throughout, $r>0$ is the discount rate, $v/r$ the social value of filling the niche, $f$ a continuous probability density with $f>0$ on its support $[\underline c,\overline c]\subset[0,\infty)$ and distribution function $F$, $\underline c<v/r<\overline c$, and the prior $h_0$ of the arrival rate satisfies Assumption 1. Let $p_{na}(\phi)$ solve (56),
--
--   $$\frac vr-p_{na}(\phi)=\frac{m_1(\phi)}{r}\int_{\underline c}^{p_{na}(\phi)}F(c)\,dc ,$$
--
--   for every $\phi\ge0$, and let $p$ have derivative $d$ at $\phi_c\ge0$ satisfying the equation of motion (24) there,
--   $F(p(\phi_c))\,d=\frac{m_2(\phi_c)}{m_1(\phi_c)}\int_{\underline c}^{p(\phi_c)}F(c)\,dc-r(\frac vr-p(\phi_c))$. If $p(\phi_c)=p_{na}(\phi_c)$, then $p_{na}$ is differentiable at $\phi_c$ and
--
--   $$p_{na}'(\phi_c)<p'(\phi_c)=d .$$
--
--   The optimal reward can therefore cross the naive reward only from below, which is the step from the asymptotics of Theorem 3 to Theorem 4.
--
--   Differences from the source:
--
--   - encoding: all ϕ; dV/dϕ, dp/dϕ → ϕ ≥ 0, derivatives within [0, ∞); reason: the state ϕ = ∫F ≥ 0 lives in ℝ₊ (the space S, p.36); one-sided derivatives at the boundary state 0
--   - generalization: the optimal reward policy p → any p with derivative d at ϕ_c satisfying (24) at ϕ_c; reason: the proof uses only (59) at ϕ_c; the optimal reward is such a p by eq_24
--   - reading: p_na(ϕ), the optimal static policy at the known arrival rate m_1(ϕ) → any p_na solving (56) at every ϕ ≥ 0; reason: the proof (p.41) works with p_na as "the unique solution to (56)"
--   - generalization: p'_na(ϕ_c) (differentiability of p_na from the implicit function theorem, p.41) → the conclusion asserts that p_na is differentiable at ϕ_c; reason: the paper states the differentiability as a fact; concluding it instead of assuming it is stronger
--   - encoding: (24) as a quotient by F(p(ϕ_c)) → (24) multiplied through by F(p(ϕ_c)); reason: at a crossing p(ϕ_c) = p_na(ϕ_c) > c̲, so F(p(ϕ_c)) > 0 and the two forms are equivalent
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, Lemma 4, Appendix p.41; proof pp.41–42, (56)–(61)

import Mathlib
import Definitions.Def_ScarceIdeas_CostDensity
import Definitions.Def_ScarceIdeas_Assumption1
import Definitions.Def_ScarceIdeas_moment
import Definitions.Def_ScarceIdeas_IsStaticReward

namespace ScarceIdeas

/-- **Lemma 4 [Single-crossing property].**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
Lemma 4, Appendix p.41; proof pp.41–42, (56)–(61).

Under the standing assumptions, let `p_na(ϕ)` solve (56),
`v/r − p_na(ϕ) = (m₁(ϕ)/r) ∫_{c̲}^{p_na(ϕ)} F(c) dc`, for every `ϕ ≥ 0`, and let `p` have derivative
`d` at `ϕ_c ≥ 0` satisfying the equation of motion (24) there,
`F(p(ϕ_c)) d = (m₂/m₁)(ϕ_c) ∫_{c̲}^{p(ϕ_c)} F − r(v/r − p(ϕ_c))`. If `p(ϕ_c) = p_na(ϕ_c)`, then
`p_na` is differentiable at `ϕ_c` and `p'_na(ϕ_c) < p'(ϕ_c) = d`.

**Formalization Note** Stated for every `p` satisfying (24) at `ϕ_c`; by (24) (milestone
`eq_24`) the optimal reward is one. (24) is multiplied through by `F(p(ϕ_c))`. Derivatives are
within `[0, ∞)`. -/
theorem lemma_4 (r v cL cH : ℝ) (f h0 : ℝ → ℝ) (hr : 0 < r) (hf : CostDensity cL cH f)
    (hvL : cL < v / r) (hvH : v / r < cH) (h0A : Assumption1 h0) (p pna : ℝ → ℝ)
    (hna : ∀ ϕ : ℝ, 0 ≤ ϕ → IsStaticReward r v cL f (moment h0 1 ϕ) (pna ϕ))
    (ϕc d : ℝ) (hϕc : 0 ≤ ϕc) (hp : HasDerivWithinAt p d (Set.Ici 0) ϕc)
    (hode : costCDF cL f (p ϕc) * d =
      moment h0 2 ϕc / moment h0 1 ϕc * (∫ c in cL..p ϕc, costCDF cL f c) - r * (v / r - p ϕc))
    (hcross : p ϕc = pna ϕc) :
    ∃ dna : ℝ, HasDerivWithinAt pna dna (Set.Ici 0) ϕc ∧ dna < d := by sorry

end ScarceIdeas
