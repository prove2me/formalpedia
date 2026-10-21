-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P43_projectionDenseCoding
-- name    : QAlgorithms.Papers.Independent.Claimed50.P43.projectionDenseCoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:18:39.986695+00:00
-- url     : https://prove2.me/theorems/c24e0bae-688c-4b4c-ad0b-7eb51d6e107c
-- title:
--   Projection-state dense-coding bound for a tensor-power channel
-- statement:
--   Let $\Phi:A\to A'$ be a CPTP channel between nonzero finite-dimensional spaces, let $n\ge1$, and let $P$ be a nonzero orthogonal projection on $A^{\otimes n}$. Write $r=\operatorname{Tr}P>0$ for its rank. With the one-shot assisted Holevo maximum and the purification-based mutual information measured in bits,
--
--   $$C_{\rm ea}^{(1)}(\Phi^{\otimes n})\ge I(P/r;\Phi^{\otimes n}).$$
--
--   The same tensor-power channel occurs on both sides. This is the dense-coding lower bound used in the capacity proof. Moreover, there is an assisted ensemble of $r^2$ equiprobable messages, with unitary local encoders, whose output Holevo information is exactly $I(P/r;\Phi^{\otimes n})$.
-- source:
--   On entanglement-assisted classical capacity, arXiv:quant-ph/0106075v2, PDF p. 3, §II, equation (7): projection-state dense-coding lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

/-- PDF p.3, (7): both occurrences of the channel are n-fold tensor powers.
Positive trace excludes the unnormalizable zero projection; trace equals projection rank.
The construction has rank(P)^2 equiprobable unitary encoders and exactly attains I(P/r;N). -/
theorem projectionDenseCoding {A C : Type} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] [Nonempty A] [Nonempty C]
    (N : Superop A C) (hN : IsChannel N) (n : ℕ) (hn : 0 < n)
    (P : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hP : P.IsHermitian) (hidem : P * P = P) (hpos : 0 < P.trace.re) :
    inputMutualInfo (piSuperop (fun _ : Fin n => N))
      ((P.trace.re : ℂ)⁻¹ • P) ≤ assistedOneShot (piSuperop (fun _ : Fin n => N)) ∧
    ∃ (m : ℕ) (e : AssistedEnsemble (Fin n → A) (m * m)),
      0 < m ∧ (m : ℝ) = P.trace.re ∧
      (∀ i, e.prob i = ((m * m : ℕ) : ℝ)⁻¹) ∧
      (∀ i, ∃ V : Matrix.unitaryGroup (Fin n → A) ℂ,
        e.encode i = conjSuperop (V : Matrix (Fin n → A) (Fin n → A) ℂ)) ∧
      assistedScore (piSuperop (fun _ : Fin n => N)) e =
        inputMutualInfo (piSuperop (fun _ : Fin n => N)) ((P.trace.re : ℂ)⁻¹ • P) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P43

end
