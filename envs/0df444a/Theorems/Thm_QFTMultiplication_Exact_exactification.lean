-- Prove2me | Theorems.Thm_QFTMultiplication_Exact_exactification
-- name    : QFTMultiplication.Exact.exactification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:55:45.179482+00:00
-- url     : https://prove2.me/theorems/872c6bd7-15a1-405f-8485-86942103fd64
-- title:
--   Lemma 3.1 — exactification of both QFT directions
-- statement:
--   Fix a full integer-multiplication family with actual gate count $M(q)$. Let $V$ be a unitary on $q$ qubits with $\|V-F_q^\dagger\|_{\mathrm{op}}\le1/2$, and let $v$ be a clean implementation using $G=|v|$ gates and $a_V$ auxiliary qubits in the stated gate model. Define, from this operator,
--   $$
--   p=2^{-q}\sum_{x=0}^{2^q-1}|\langle x|V|\phi_x\rangle|^2,
--   \qquad \theta_q=\arcsin\!\left(\frac1{2\sqrt p}\right).
--   $$
--   The preamble's consequences are $p\ge3/4$ and $p\sin^2\theta_q=1/4$. Exact unit-cost access to $B(\theta_q)$, in addition to the basic gates, permits exact clean implementations of both transforms, with positive constants $C_g,C_a$ chosen before all $q,V,v,a_V$:
--   $$
--   |c_F|,|c_{F^\dagger}|\le C_g(G+M(q)),\qquad
--    a_F,a_{F^\dagger}\le C_a(a_V+M(q)).
--   $$
--   Every auxiliary qubit returns to zero, and equality includes global phase. The input implementation and both output directions may use only H, CNOT, dyadic phases, and this same additional angle; its inverse is obtained at constant cost rather than admitted as another rotation type. This conversion connects constant-error Fourier circuits to the exact target.
--
--   **Formalization Note** The lower bound on $p$ and the quarter-success identity are conclusions, not extra assumptions. Neither an exact QFT circuit nor a correct reversible multiplier is assumed as input. Only the actual classical multiplication DAG and the given approximate circuit are supplied.
--
--   Differences from the source:
--   - encoding: equality on all quantum states with clean auxiliaries → literal equality on all complex vectors with clean auxiliaries; reason: linearity makes these conditions equivalent, including preservation of global phase
--   - encoding: O-bounds → positive real gate and auxiliary constants before every register size; reason: this is the family-level asymptotic meaning, with allowable dependence only on the fixed data
--   - encoding: resource functions G(q), a(q) of a chosen clean implementation → the actual list length |v| and actual auxiliary count a_V, uniformly over implementations; reason: these are the displayed resource functions evaluated at q, with no assumed exactness invariant
--   - encoding: the preamble asserts p≥3/4 and quarter success after B → these consequences appear alongside the exact circuit conclusion; reason: they are derived obligations and do not restrict the input approximation
--   - encoding: the stated gate model and exact access to the additional rotation → input and output implementations over the same exactGates(exactAngle q V); reason: this retains every permitted circuit witness and adds no other primitive rotation
-- source:
--   Chandrima Kayal, Rajat Mittal, Manaswi Paraashar, Nitin Saurabh, STOC 2027 submission #1075 (October 2026), Lemma 3.1 and its Section 3 preamble, Equations (7)–(8), pp. 8–11 (PDF pp. 8–11)

import Definitions.Def_QFTMultiplication_Exact_Model

set_option autoImplicit false

namespace QFTMultiplication.Exact

open QAlgorithms

/-- Lemma 3.1, p.9, with the full pp.8–9 preamble. Constants are independent of
q,V and its chosen implementation over the source's one-angle gate set. The additional angle is computed from V.
The p≥3/4 consequence is not a hypothesis. Forward and inverse use the same one-angle set. -/
theorem exactification
    (F : (n : ℕ) → BoolCircuit (n + n) (2 * n)) (hF : MultCorrect F) :
    ∃ Cg Ca : ℝ, 0 < Cg ∧ 0 < Ca ∧
      ∀ (q : ℕ) (V : Op q) (aV : ℕ) (v : Circuit (exactGates (exactAngle q V)) (q + aV)),
        V ∈ Matrix.unitaryGroup (Qubits q) ℂ →
        specNorm (V - star (qftQubits q)) ≤ 1 / 2 → CleanImplements v V →
        3 / 4 ≤ averageSuccess q V ∧
        averageSuccess q V * Real.sin (exactAngle q V) ^ 2 = 1 / 4 ∧
        ∃ (af ai : ℕ)
          (cf : Circuit (exactGates (exactAngle q V)) (q + af))
          (ci : Circuit (exactGates (exactAngle q V)) (q + ai)),
          CleanImplements cf (qftQubits q) ∧
          CleanImplements ci (star (qftQubits q)) ∧
          (cf.size : ℝ) ≤ Cg * (v.size + multSize F q) ∧
          (ci.size : ℝ) ≤ Cg * (v.size + multSize F q) ∧
          (af : ℝ) ≤ Ca * (aV + multSize F q) ∧
          (ai : ℝ) ≤ Ca * (aV + multSize F q) := by sorry

end QFTMultiplication.Exact
