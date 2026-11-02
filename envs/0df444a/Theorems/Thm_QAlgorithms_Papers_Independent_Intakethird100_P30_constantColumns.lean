-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P30_constantColumns
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P30.constantColumns
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:39:44.3102+00:00
-- url     : https://prove2.me/theorems/09f7e536-467c-458e-b719-3ff3b1e4ceca
-- title:
--   II B: removal of constant columns preserves threshold, (8)
-- statement:
--   Let $C=(C_k)_{k\in K}$ be a nonempty code of distinct $n$-bit words, $n\ge1$. Separate its coordinates into the fixed coordinates $F$ and the varying coordinates $V$. Let $D_k=C_k|_V$, and let $\beta=C_{k_0}|_F$ for any chosen codeword $k_0$; the latter does not depend on the chosen word. The residual words remain distinct and have no constant coordinates. For the Bob-only filtered operators, explicit restriction of Alice's coordinate register gives
--
--   $$P_C(Q)=P_{\{\beta\}}(Q)\otimes P_D(Q),\qquad
--   \mathrm{Ext}_B(P_{\{\beta\}}(Q)),\qquad Q_C^*=Q_D^*
--   \quad(0\le Q\le\tfrac12).$$
--
--   The singleton factor has a one-dimensional Bob register. This retains the full factorization underlying column deletion. A singleton original code can leave a zero-length residual register, which is only a helper case and has threshold zero.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, PDF p. 4, II B: removal of constant columns preserves threshold, (8)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}

variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [Fintype A] [Fintype B]

/-- PDF p.4, (8): deletion of every constant column, with full factorization
under coordinate restriction and the extendable one-dimensional-B factor.
The residual coordinate register may be empty for a singleton code. -/
theorem constantColumns {n : ℕ} (hn : 1 ≤ n) [Nonempty K]
    (C : K → Qubits n) (hC : Function.Injective C) (k0 : K) :
    Function.Injective (deleteConstants C) ∧ NoConstantColumns (deleteConstants C) ∧
    (∀ Q : ℝ, 0 ≤ Q → Q ≤ 1 / 2 →
      BobExtendible (bobState (fun _ : Unit => fun i : FixedCoordinates C => C k0 i.val) Q) ∧
      ∀ (a a2 : Qubits n) (k l : K),
        bobState C Q (a, k) (a2, l) =
          bobState (fun _ : Unit => fun i : FixedCoordinates C => C k0 i.val) Q
            ((fun i => a i.val), ()) ((fun i => a2 i.val), ()) *
          bobState (deleteConstants C) Q
            ((fun i => a i.val), k) ((fun i => a2 i.val), l)) ∧
    bobThreshold C = bobThreshold (deleteConstants C) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P30

end
