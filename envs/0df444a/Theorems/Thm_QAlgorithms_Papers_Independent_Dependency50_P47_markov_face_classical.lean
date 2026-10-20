-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P47_markov_face_classical
-- name    : QAlgorithms.Papers.Independent.Dependency50.P47.markov_face_classical
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:43:10.636623+00:00
-- url     : https://prove2.me/theorems/9f53abd4-726c-492e-91f3-54e760b47b79
-- title:
--   §4 Example: equality of classical and quantum conditional-entropy regions on the Markov face
-- statement:
--   Let $X_1,X_2$ have any normalized joint law on finite nonempty alphabets, let $X_3=(X_1,X_2)$ deterministically, and let $F$ be any finite-dimensional quantum extension of that law. If
--
--   $$
--   H(X_1X_2\mid F)=H(X_1\mid F)+H(X_2\mid F),
--   $$
--
--   there is a finite classical extension $C$ of the same pair law such that $I(X_1;X_2\mid C)=0$ and
--
--   $$
--   H(X_i\mid C)=H(X_i\mid F)\ (i=1,2),\qquad
--   H(X_1X_2\mid C)=H(X_1X_2\mid F).
--   $$
--
--   Hence the three-coordinate classical and quantum entropy regions coincide on this face. No user-supplied strong-subadditivity decomposition is assumed.
-- source:
--   On Dimension Bounds for Auxiliary Quantum Systems, arXiv:1207.3911v4, PDF p. 9, §4 Example: equality of classical and quantum conditional-entropy regions on the Markov face

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P47

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Information100.P48 (normalize)

open QAlgorithms.Papers.Independent.Information100.P62 (IsProjection)

/-- §4 Example, PDF pp.9–10: X3 is the pair, and all three coordinates are matched. -/
theorem markov_face_classical {n k d : ℕ} (hn : 0 < n) (hk : 0 < k) (hd : 0 < d)
    (p : Law (Fin n × Fin k)) (Q : QChannel (Fin n × Fin k) (Fin d))
    (hface : qCond p.prob Q.rho id = qCond p.prob Q.rho Prod.fst + qCond p.prob Q.rho Prod.snd) :
    ∃ c : ℕ, 0 < c ∧ ∃ K : CChannel (Fin n × Fin k) (Fin c),
      cCond p.prob K Prod.fst = qCond p.prob Q.rho Prod.fst ∧
      cCond p.prob K Prod.snd = qCond p.prob Q.rho Prod.snd ∧
      cCond p.prob K id = qCond p.prob Q.rho id ∧
      cCond p.prob K Prod.fst + cCond p.prob K Prod.snd - cCond p.prob K id = 0 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P47

end
