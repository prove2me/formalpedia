-- Prove2me | Theorems.Thm_PauliUnclonable531_Pauli_headline_encryption
-- name    : PauliUnclonable531.Pauli.headline_encryption
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:22.363278+00:00
-- url     : https://prove2.me/theorems/b85ee9e2-df14-4af6-8858-15bd07942526
-- title:
--   Theorem 1.1 — efficient perfectly correct encryption with the exact unclonable bound
-- statement:
--   There exists the explicit Section 3 family of one-time private-key schemes for one-bit messages. For every n≥1 its key is exactly uniform on the 4ⁿ−1 nonidentity n-qubit Pauli labels, encoded injectively by 2n classical bits, and its ciphertext is an n-qubit density operator. Its decryption effects form a valid binary POVM, with perfect correctness for every supported key and message.
--
--   The generated Section 3.1 encryption instructions have their actual H,S,X matrix semantics and realize the prescribed ciphertext ensemble. They use exactly n−1 independent fair bits, n computational-basis preparations, and at most 2n H/S gates; each basis preparation uses at most one X on a fresh zero qubit. The pivot is the least nonidentity position. These single-qubit gates are unitary and normalize the Pauli family up to sign, giving the asserted Clifford implementation. Generated decryption uses at most n local Pauli measurements and its Born outcome law equals the global two-projector measurement for every input density operator, including entangled inputs. Under the declared address-bit cost model both classical costs are bounded uniformly by 100(n+1)².
--
--   Against every finite-dimensional information-theoretic attack, including randomized challenge-message selection with associated auxiliary preparation, the full game satisfies
--
--   $$\Pr[b_B=b_C=b]\le\frac12+\frac12\sqrt{\frac{2^n}{4^n-1}}.$$
--
--   Correctness, physical validity, operational semantics, resource counts and security are conclusions for the constructed family. None is assumed in a scheme or attack record.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert-space operators and binary strings → complex matrices indexed by finite computational bases, Fin 2 bits, real Born probabilities, Euclidean spectral norm and PSD-difference order; reason: these are the same finite-dimensional objects and conventions after choosing the source basis
--   - encoding: efficient encryption and decryption by the p.16–17 instructions → the concrete uniform instruction generators and Born interpreters, with exact draw/preparation/measurement counts and both address-bit costs at most 100(n+1)²; reason: 100 bounds the charged lengths of these particular procedures in the declared bit model; it is independent of n, key, message and attack, and changes no security constant
--   - encoding: the general one-bit message-selection game → a distribution on four classical message pairs and arbitrary conditional CPTP/local-POVM attacks; reason: conditioning absorbs the auxiliary preparation exactly as in Remark 2.12
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Theorem 1.1 (Informal), p.3; Definitions 2.9–2.11 and Remark 2.12, pp.14–15; §3.1, pp.16–17; Theorem 4.1, p.17

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Game
import Definitions.Def_PauliUnclonable531_Pauli_Ensemble

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

/-- Full Theorem 1.1, p.3, with the concrete §3.1 implementation. The fixed coefficient
100 is a conservative bookkeeping bound for the declared address-bit cost of the actual
lists; it is not a security constant. H,S,X have their actual matrices, and local
measurement semantics include entangled inputs. -/
theorem headline_encryption :
    ∃ family : (n : ℕ) → Scheme n, family = explicitScheme ∧
      (∀ g : Gate, (gateMatrix g).conjTranspose * gateMatrix g = 1 ∧
        ∀ p : Fin 4, ∃ q : Fin 4, ∃ b : Fin 2,
          gateMatrix g * QMaxCutSDP.Rounding.pauli p * (gateMatrix g).conjTranspose =
            sign b • QMaxCutSDP.Rounding.pauli q) ∧
      ∀ n : ℕ, 1 ≤ n →
        Fintype.card (Key n) = 4^n - 1 ∧
        Function.Injective (@keyEncode n) ∧
        Fintype.card (Fin (n+n)) = 2*n ∧
        Fintype.card (Bits n) = 2^n ∧
        (∀ k, (family n).gen k = (Fintype.card (Key n) : ℝ)⁻¹ ∧ 0 < (family n).gen k) ∧
        (∑ k : Key n, (family n).gen k) = 1 ∧
        (∀ k m, Density ((family n).enc k m)) ∧
        (∀ k, (∀ m, ((family n).dec k m).PosSemidef) ∧ (∑ m, (family n).dec k m) = 1) ∧
        (∀ k m, born ((family n).dec k m) ((family n).enc k m) = 1) ∧
        (∀ k m, operationalEnc k m = (family n).enc k m) ∧
        (∀ k : Key n, (∃ j, pivot k = some j ∧ active k.val j = true ∧
                    ∀ i : Fin n, i < j → active k.val i = false) ∧
          Fintype.card (Tape k) = 2^(n-1) ∧
          fairCount (encProgram k) = n-1 ∧ preparationCount (encProgram k) = n ∧
          gateCount (encProgram k) ≤ 2*n ∧ encBitCost k ≤ 100*(n+1)^2) ∧
        (∀ k (σ : Op (Bits n)), Density σ → ∀ b : Fin 2,
          operationalDec k σ b = born ((family n).dec k b) σ) ∧
        (∀ k : Key n, (decProgram k).length ≤ n ∧ decBitCost k ≤ 100*(n+1)^2) ∧
        (∀ (B C : Type) [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
            [Nonempty B] [Nonempty C] (a : GeneralAttack n B C),
          generalWin (family n) a ≤ 1/2 + (1/2) * Real.sqrt ((2 : ℝ)^n / ((4 : ℝ)^n - 1))) := by sorry

end PauliUnclonable531.Pauli
