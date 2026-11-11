-- Prove2me | Theorems.Thm_TDHamSim_QueryOptimal_lemma_5
-- name    : TDHamSim.QueryOptimal.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:23:08.158887+00:00
-- url     : https://prove2.me/theorems/406a321f-4392-40a1-8536-a23e08e32cf4
-- title:
--   Lemma 5 — reuse error identity
-- statement:
--   Let $H$ and its Hermitian-unitary HAM-T blocks satisfy the standing assumptions, with $J=2^m$ and $0<\alpha T/J\le1$. Let the reuse register have $b$ qubits and let $1\le N<2^b$. With $A,C$ the private and cross blocks of $S$, and with $P_N$ computed by the finite reuse circuit,
--
--   $$U_C-P_N=C\,G_N(A)\Gamma.$$
--
--   The zero-private-input error is thus an exact operator identity. The uniform preparation is completed explicitly; changing its other columns leaves this compression unchanged.
--
--   Differences from the source:
--   - encoding: qubit Hilbert spaces, tensor registers and time labels → binary-string bases, finite coordinate matrices and Fin indices with the spectral norm; reason: a change of coordinates representing every source instance, with explicit direct-sum and flag encodings
--   - encoding: an unspecified unitary completion of a uniform state preparation F_N → the explicit real Householder completion of that uniform column; reason: P_N depends only on the uniform column; this fixes a source choice without changing the encoded operator
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), Lemma 5 — reuse error identity, p.18. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_LCU

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

/-- Lemma 5, p.18: P_N is computed from the reuse circuit (32), not from this identity. -/
theorem lemma_5 {n a : ℕ} (m b N : ℕ) (H : ℝ → Mat (Bits n))
    (O : Fin (2^m) → Mat (Bits a × Bits n)) (α β T : ℝ)
    (hα : 0 < α) (hβ : 0 ≤ β) (hT : 0 < T) (hw : stepWeight α T (2^m) ≤ 1)
    (hH : IsHamiltonian H α β T) (hO : IsHAMT H α T O) (hN : 1 ≤ N) (hNb : N < 2^b) :
    cayleyProduct H α T (2^m) - reuseP b N (stepWeight α T (2^m)) O =
      crossBlock (stepWeight α T (2^m)) O * G N (privateBlock (stepWeight α T (2^m)) O) * gamma H α T O := by sorry

end TDHamSim.QueryOptimal
