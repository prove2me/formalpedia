-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P15_repetitionCode_logicalError_and_probability
-- name    : QAlgorithms.Papers.Independent.Advance50.P15.repetitionCode_logicalError_and_probability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:24:53.545136+00:00
-- url     : https://prove2.me/theorems/2d7d58a8-3668-456b-b004-35fd92fd3ea2
-- title:
--   Repetition-code logical Pauli error and exact syndrome probability
-- statement:
--   Let $m\ge1$, let $u,v\in\{0,1\}^m$ be physical bit- and phase-error strings, and let $|\psi\rangle=\alpha|0\rangle+\beta|1\rangle$ have unit norm. Encode it as $\alpha|0\rangle^{\otimes m}+\beta|1\rangle^{\otimes m}$. The coherent repetition decoder retains the first physical qubit and writes the $Z_1Z_j$ check outcomes into an $(m-1)$-bit syndrome register. With $Z$ acting before $X$, it satisfies
--
--   $$
--   D_m X^u Z^v\operatorname{Enc}_m|\psi\rangle
--    = \left(X^{u_1}Z^{\bigoplus_{j=1}^m v_j}|\psi\rangle\right)
--      \otimes |u_1\oplus u_2,\ldots,u_1\oplus u_m\rangle.
--   $$
--
--   Independently, let the physical bit errors be independent Bernoulli random variables of parameter $p\in[0,1]$. For a logical bit error $a\in\{0,1\}$ and a particular syndrome string $s\in\{0,1\}^{m-1}$ of Hamming weight $w$, their joint probability is
--
--   $$
--   P_m^p(a,s)=
--   \begin{cases}
--   p^{m-w}(1-p)^w,&a=1,\\
--   p^w(1-p)^{m-w},&a=0.
--   \end{cases}
--   $$
--
--   This gives the exact logical channel and syndrome law used in the block-rate calculation. The probability is for an individual syndrome, with no binomial coefficient and with $x^0=1$ at the endpoints.
--
--   **Formalization Note** Lean writes $m=k+1$ for $k\in\mathbb N$; source qubit 1 is Lean wire 0.
-- source:
--   Structured Codes Improve the Bennett-Brassard-84 Quantum Key Rate, arXiv:quant-ph/0607018v2, PDF p. 2, Lemma 2 / Eq. (3)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P15

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P15

open QAlgorithms

open scoped ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Smith--Renes--Smolin, PDF p.2, Lemma 2 / Eq.(3): exact ordered-Pauli
logical action and the logical-bit/specific-syndrome law of independent errors.
There is no binomial coefficient and no majority decoder. -/
theorem repetitionCode_logicalError_and_probability
    (k : ℕ) (u v : Qubits (k + 1))
    (psi : EuclideanSpace ℂ Bool) (hpsi : ‖psi‖ = 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    repetitionDecode (physicalPauli u v (repetitionEncode k psi)) =
      WithLp.toLp 2 (fun z : Bool × Qubits k =>
        logicalPauli (u 0) (dotBits v (fun _ => true)) psi z.1 * (ket (repetitionSyndrome u)) z.2) ∧
    ∀ (a : Bool) (s : Qubits k),
      logicalSyndromeProb k p a s =
        if a then p ^ (k + 1 - hammingWeight s) * (1 - p) ^ hammingWeight s
        else p ^ hammingWeight s * (1 - p) ^ (k + 1 - hammingWeight s) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P15

end
