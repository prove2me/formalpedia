-- Prove2me | Theorems.Thm_QuantumLTF_Membership_lemma_3_2
-- name    : QuantumLTF.Membership.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:37:55.921537+00:00
-- url     : https://prove2.me/theorems/66afdbd5-dc6a-4d91-a535-2a58102f14f4
-- title:
--   Lemma 3.2 — large thresholds are almost constant
-- statement:
--   Let $n\ge2$, $w\in\mathbb S^{n-1}$, $\theta\in\mathbb R$, $0<\epsilon<1$. If $|\theta|\ge\sqrt{2\log(1/\epsilon)}$, the constant function $c\equiv f_{w,\theta}(0)$, obtained from one membership query at the origin, satisfies
--   $$\Pr_{x\sim\gamma_n}[f_{w,\theta}(x)\ne c(x)]\le\epsilon.$$
--   This disposes of the regime of large thresholds, so the learner may assume that the boundary is close to the origin.
--
--   Differences from the source:
--   - reading: a single membership query suffices to output a constant function c → c is the constant with value f_{w,θ}(0); reason: the proof on p. 21 gives this query and this output; naming them is the strongest reading of the sentence
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Lemma 3.2, Eq. (25), p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_disagree

namespace QuantumLTF.Membership

/-- **Lemma 3.2 (large thresholds are almost constant).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Lemma 3.2, p. 21 (PDF p. 22),
Eq. (25). For `n ≥ 2`, unit `w`, `θ`, and `0 < ϵ < 1` with `|θ| ≥ √(2 log(1/ϵ))`, one membership query
suffices to output a constant function `c` with `Pr[f_{w,θ} ≠ c] ≤ ϵ`.

**Formalization Note.** The single query is at the origin (proof, p. 21): `c` is the constant
function with the value `f_{w,θ}(0)`, so the statement names the query and the output. -/
theorem lemma_3_2 {n : ℕ} (hn : 2 ≤ n) (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) (θ ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) (hθ : Real.sqrt (2 * Real.log (1 / ε)) ≤ |θ|) :
    disagree (ltf w θ) (fun _ => ltf w θ 0) ≤ ε := by sorry

end QuantumLTF.Membership
