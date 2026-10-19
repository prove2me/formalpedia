-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_woottersXSpecialization
-- name    : QAlgorithms.Papers.Independent.Information100.P21.woottersXSpecialization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:05:36.202606+00:00
-- url     : https://prove2.me/theorems/752492f9-b026-43a3-b090-05776887ce27
-- title:
--   V.A — specialization of the claimed Wootters formula
-- statement:
--   For a canonical real X state with positive diagonal entries and strict physicality $w^2<ad$, $z^2<bc$, Wootters pairs can satisfy
--   $$\lambda_{e,\pm}=\sqrt{ad}\pm w,\quad K_{e,\pm}=\kappa_e=\frac{a+d}{2\sqrt{ad}},\qquad\lambda_{o,\pm}=\sqrt{bc}\pm z,\quad K_{o,\pm}=\kappa_o=\frac{b+c}{2\sqrt{bc}}.$$
--   All four numbers are positive. After sorting the numbers and associated norms together, the earlier candidate is $C\min\{\kappa_o,(\kappa_e+\kappa_o)/2\}$ in the entangled $w$ sector and $C\min\{\kappa_e,(\kappa_e+\kappa_o)/2\}$ in the entangled $z$ sector. Here $C=2(w-\sqrt{bc})$ or $2(z-\sqrt{ad})$, respectively. This specializes the candidate without identifying it with robustness.
--
--   In the w-entangled branch, the mixed-state concurrence is $C(\rho_X)=2(w-\sqrt{bc})$; in the z-entangled branch it is $C(\rho_X)=2(z-\sqrt{ad})$.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 15, V.A — specialization of the claimed Wootters formula

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF pp.15–16, specialization of the claimed Wootters formula.
Includes the branch concurrence identities stated beside S81–S82. -/
theorem woottersXSpecialization (a b c d w z : ℝ) (h : physicalX a b c d w z)
  (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (hw : w^2<a*d) (hz : z^2<b*c) :
  let lam : Fin 4 → ℝ := ![Real.sqrt (a*d)+w,Real.sqrt (a*d)-w,Real.sqrt (b*c)+z,Real.sqrt (b*c)-z]
  let ke := (a+d)/(2*Real.sqrt (a*d))
  let ko := (b+c)/(2*Real.sqrt (b*c))
  let K : Fin 4 → ℝ := ![ke,ke,ko,ko]
  (∃ v : Fin 4 → Vec QQ, woottersFrame (xstate a b c d w z) lam v ∧
    ∀ i, frameNorm lam v i=K i) ∧
  (∀ i,0<lam i) ∧ (∃ p : Equiv.Perm (Fin 4), Antitone (fun i => lam (p i))) ∧
  (b*c<w^2 → concurrence (xstate a b c d w z) = 2*(w-Real.sqrt (b*c))) ∧
  (a*d<z^2 → concurrence (xstate a b c d w z) = 2*(z-Real.sqrt (a*d))) ∧
  (∀ p : Equiv.Perm (Fin 4), Antitone (fun i => lam (p i)) →
    (b*c<w^2 → oldCandidate (fun i => lam (p i)) (fun i => K (p i))=
      2*(w-Real.sqrt (b*c))*min ko ((ke+ko)/2)) ∧
    (a*d<z^2 → oldCandidate (fun i => lam (p i)) (fun i => K (p i))=
      2*(z-Real.sqrt (a*d))*min ke ((ke+ko)/2))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
