-- Prove2me | Theorems.Thm_QRepeaterBench_Dephasing_eq_91
-- name    : QRepeaterBench.Dephasing.eq_91
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:39.868767+00:00
-- url     : https://prove2.me/theorems/bcdfc37a-8348-4bca-9d1c-5c7f48f3a82b
-- title:
--   Eq. (91) — the von Neumann entropy of the Choi matrix of P_d equals the Shannon entropy H(P) of the weights P_m(p,d)
-- statement:
--   Let $d\ge2$ and $p\in[0,1]$. The von Neumann entropy (in bits) of the Choi matrix of the qudit dephasing channel equals the Shannon entropy of the binomial weights:
--
--   $$S(\rho_{\mathcal P_d})=H(\mathbf P)=-\sum_{m=0}^{d-1}P_m(p,d)\log_2P_m(p,d).$$
--
--   The paper reaches this by diagonalizing $\rho_{\mathcal P_d}$; its nonzero spectrum consists of the nonzero weights $P_m(p,d)$. The identity gives the first term of the relative entropy $S(\rho_{\mathcal P_d}\|\tilde\sigma)$ and, through Eq. (45), the coherent information of the channel.
--
--   **Formalization Note** Only the entropy identity is stated, for every $p\in[0,1]$ with the convention $0\log 0=0$. The paper's phrase "$d$ non-zero eigenvalues" fails at $p\in\{0,1\}$, where some $P_m$ vanish; the entropy identity is unaffected.
-- source:
--   Pirandola & Laurenza, General Benchmarks for Quantum Repeaters, arXiv:1512.04945v2, p. 11, Eq. (91)

import Mathlib
import Definitions.Def_QRepeaterBench_Dephasing_Model

open scoped Matrix ENNReal

namespace QRepeaterBench.Dephasing
theorem eq_91 (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : QAlgorithms.vnEntropy (choi d (dephasing d p)) = shannonEntropy (weight d p) := by sorry
end QRepeaterBench.Dephasing
