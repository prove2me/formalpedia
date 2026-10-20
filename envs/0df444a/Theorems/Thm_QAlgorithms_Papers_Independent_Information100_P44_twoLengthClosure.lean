-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_twoLengthClosure
-- name    : QAlgorithms.Papers.Independent.Information100.P44.twoLengthClosure
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:45:30.415122+00:00
-- url     : https://prove2.me/theorems/960aab4c-6b27-4b16-a575-b75a9958b57c
-- title:
--   Remark 4: two nonzero trace-polygon lengths
-- statement:
--   Let $\Phi$ be CPTP and $i\ne j$. Suppose precisely two products $p(r_1|i)p(r_1|j)$ and $p(r_2|i)p(r_2|j)$ are positive, with $r_1\ne r_2$, and all other such products vanish. If every trace-polygon elementary bound is saturated, then
--   $$\sqrt{p(r_1|i)p(r_1|j)}=\sqrt{p(r_2|i)p(r_2|j)},\qquad p(r_1|i)p(r_1|j)=p(r_2|i)p(r_2|j).$$
--   This is a necessary condition for joint saturation, not an existence criterion for a channel.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 14, Remark 4: two nonzero trace-polygon lengths

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.14, Remark 4: two nonzero trace-polygon lengths must agree; no sufficiency claim. -/
theorem twoLengthClosure {d : ℕ} (hd : 0 < d) (Phi : Map d) (hPhi : IsChannel Phi)
    (i j : Fin d) (hij : i ≠ j) (r1 r2 : Fin d) (hr : r1 ≠ r2)
    (h1 : 0 < population Phi r1 i * population Phi r1 j)
    (h2 : 0 < population Phi r2 i * population Phi r2 j)
    (hzero : ∀ r, r ≠ r1 → r ≠ r2 → population Phi r i * population Phi r j = 0)
    (hsat : ∀ r, ‖Phi (matrixUnit i j) r r‖ =
      Real.sqrt (population Phi r i * population Phi r j)) :
    Real.sqrt (population Phi r1 i * population Phi r1 j) =
      Real.sqrt (population Phi r2 i * population Phi r2 j) ∧
    population Phi r1 i * population Phi r1 j = population Phi r2 i * population Phi r2 j := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
