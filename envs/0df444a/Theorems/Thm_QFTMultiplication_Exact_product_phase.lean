-- Prove2me | Theorems.Thm_QFTMultiplication_Exact_product_phase
-- name    : QFTMultiplication.Exact.product_phase
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:55:52.363038+00:00
-- url     : https://prove2.me/theorems/e618164c-fc31-4477-8fd3-c134219742ae
-- title:
--   Lemma 2.1 — product-phase operation
-- statement:
--   Fix any well-formed Boolean multiplication family and let $M(q)$ count its gates. There are positive constants $C_g,C_a$, independent of $q,d$ and the sign, such that for every $q$, every $1\le d\le2q$, and either sign, there is an exact clean circuit on two designated $q$-qubit registers and $a$ temporary qubits with
--   $$
--   |A\rangle|B\rangle\longmapsto e^{\pm2\pi iAB/2^d}|A\rangle|B\rangle,
--   \qquad |c|\le C_gM(q),\qquad a\le C_aM(q).
--   $$
--   The action holds coherently for every pair of unsigned $q$-bit integers. All temporary qubits return to zero. Only Hadamard, CNOT, and the dyadic phases of Equation (3) are used. This operation supplies the multiplication-dependent phase primitive used by the other circuits.
--
--   Differences from the source:
--   - encoding: equality on all quantum states with clean auxiliaries → literal equality on all complex vectors with clean auxiliaries; reason: linearity makes these conditions equivalent, including preservation of global phase
--   - encoding: O-bounds → positive real gate and auxiliary constants before every register size; reason: this is the family-level asymptotic meaning, with allowable dependence only on the fixed data
-- source:
--   Chandrima Kayal, Rajat Mittal, Manaswi Paraashar, Nitin Saurabh, STOC 2027 submission #1075 (October 2026), Lemma 2.1, p. 6 (PDF p. 6)

import Definitions.Def_QFTMultiplication_Exact_Model

set_option autoImplicit false

namespace QFTMultiplication.Exact

open QAlgorithms

/-- Lemma 2.1, p.6. Both signs and every 1≤d≤2q; constants precede q,d,sign. -/
theorem product_phase
    (F : (n : ℕ) → BoolCircuit (n + n) (2 * n)) (hF : MultCorrect F) :
    ∃ Cg Ca : ℝ, 0 < Cg ∧ 0 < Ca ∧
      ∀ (q d : ℕ) (neg : Bool), 1 ≤ d → d ≤ 2 * q →
        ∃ (a : ℕ) (c : Circuit baseGates ((q + q) + a)),
          CleanImplements c (productPhase q d neg) ∧
          (c.size : ℝ) ≤ Cg * multSize F q ∧ (a : ℝ) ≤ Ca * multSize F q := by sorry

end QFTMultiplication.Exact
