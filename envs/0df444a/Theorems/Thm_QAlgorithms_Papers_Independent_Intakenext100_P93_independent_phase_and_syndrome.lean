-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P93_independent_phase_and_syndrome
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P93.independent_phase_and_syndrome
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:37:15.689935+00:00
-- url     : https://prove2.me/theorems/fe1187a5-a1db-4bfd-b827-5c724ab2318a
-- title:
--   Repetition Lengths for Almost Bitflip Channels: logical phase law and syndrome concentration
-- statement:
--   Let $q_x,q_z\in[0,1]$ and let each physical qubit have independent amplitude and phase errors: $p_x=q_x(1-q_z)$, $p_y=q_xq_z$, and $p_z=q_z(1-q_x)$. For the cat of length $m=k+1$, write $V$ for the parity of all physical phase errors and $S$ for its retained syndrome. Then $V$ and $S$ are independent, including impossible syndromes, and
--
--   $$
--   \Pr(V=1)=\frac{1-(1-2q_z)^m}{2},\qquad
--   \Pr(V=v,S=s)=\Pr(V=v)\Pr(S=s).
--   $$
--
--   For $0\le r\le k$, the weight $W=|S|$ has the exact law
--
--   $$
--   \Pr(W=r)=\binom kr\left[(1-q_x)q_x^r(1-q_x)^{k-r}+q_x(1-q_x)^rq_x^{k-r}\right].
--   $$
--
--   For every $\epsilon>0$, its mass outside both normalized centers converges to zero:
--
--   $$
--   \lim_{k\to\infty}\Pr\!\left(\min\{|W/k-q_x|,|W/k-(1-q_x)|\}>\epsilon\right)=0.
--   $$
--
--   The empty syndrome at $k=0$ has a separately defined zero tail mass. The centers may coincide at $q_x=1/2$; no inference of a logical amplitude error is claimed there. This states the phase law and qualitative two-center concentration without adding a finite tail exponent.
-- source:
--   Degenerate Quantum Codes for Pauli Channels, arXiv:quant-ph/0604107v2, PDF p. 2, Repetition Lengths for Almost Bitflip Channels: logical phase law and syndrome concentration

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P93

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P93

open QAlgorithms

open scoped BigOperators ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Smith--Smolin, PDF pp.2--3, Repetition Lengths for Almost Bitflip Channels:
phase parity is independent of the entire syndrome; syndrome weight is a
mixture of two binomials and concentrates near k qx and k(1-qx).
The centers may coincide and the endpoint distributions may be deterministic. -/
theorem independent_phase_and_syndrome (qx qz : ℝ)
    (hx0 : 0 ≤ qx) (hx1 : qx ≤ 1) (hz0 : 0 ≤ qz) (hz1 : qz ≤ 1) :
    (∀ (k : ℕ) (s : Qubits k) (v : Bool),
      (∑ u : Bool, catLogicalSyndromeMass k (qx * (1 - qz)) (qx * qz) (qz * (1 - qx)) u v s) =
        (if v then (1 - (1 - 2 * qz) ^ (k + 1)) / 2
          else (1 + (1 - 2 * qz) ^ (k + 1)) / 2) *
        iidCatSyndromeMass k (qx * (1 - qz)) (qx * qz) (qz * (1 - qx)) s) ∧
    (∀ k : ℕ, (∑ s : Qubits k, ∑ u : Bool,
      catLogicalSyndromeMass k (qx * (1 - qz)) (qx * qz) (qz * (1 - qx)) u true s) =
        (1 - (1 - 2 * qz) ^ (k + 1)) / 2) ∧
    (∀ (k r : ℕ), r ≤ k →
      syndromeWeightMass k (qx * (1 - qz)) (qx * qz) (qz * (1 - qx)) r =
        (Nat.choose k r : ℝ) *
          ((1 - qx) * qx ^ r * (1 - qx) ^ (k - r) +
            qx * (1 - qx) ^ r * qx ^ (k - r))) ∧
    (∀ epsilon : ℝ, 0 < epsilon →
      Filter.Tendsto (fun k : ℕ => concentrationTail k qx qz epsilon)
        Filter.atTop (nhds 0)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P93

end
