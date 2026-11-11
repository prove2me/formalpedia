-- Prove2me | Theorems.Thm_PermSymQuery_Quadratic_lemma_3_3
-- name    : PermSymQuery.Quadratic.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:14:16.665909+00:00
-- url     : https://prove2.me/theorems/0edcd9fc-0a57-4d87-b587-626bc067a97f
-- title:
--   Lemma 3.3 — combined query approximation and isometry
-- statement:
--   Let $q,N,s$ be natural numbers satisfying $q\ge1$, $q+1<s<N$, and $3q+2\le N$. Define $W=J_sV_N$ using the concrete compressed-permutation map $V_N$. Then $W$ preserves the norm of every vector in $H_{\le q+1}$. For every address $i\in[N]$ and every integer $0\le t\le q$,
--   $$\left\|(\widehat O_iW-WP_i)\Pi_{\le t}\right\|\le\eta_{N,s,q}=\frac{60}{\sqrt{N-q}}+\frac{q+1}{N-2q-1}+2\sqrt{\frac2{s-q-1}}.$$
--   The identity on the answer register is understood in this formula. The subspace $H_{\le r}$ is spanned by completion states with at most $r$ records, $\Pi_{\le t}$ is its orthogonal projector, and $P_i$ is the purified permutation query. Every denominator is positive. These are two conclusions about defined maps; the compressed-oracle approximation theorem is not assumed as a hypothesis.
--
--   Differences from the source:
--   - encoding: sampled direct sum and maps defined on the stated low database levels → valid pairs span a subspace of the product-basis Euclidean space, with J_s zero off its domain; reason: compression and lookup preserve validity, and every use of J_s is restricted to the source levels
--   - encoding: identities on the answer register are implicit → tensor products with the answer identity and with the low-degree projector are explicit; reason: this gives the same operator norm on the same Hilbert space
-- source:
--   Yunqi Huang, Lvzhou Li, Zekun Ye, Shenggen Zheng, Optimal Separations Between Randomized and Quantum Query Complexity under Permutation Symmetry, STOC 2027 submission #1644 (October 2026), Lemma 3.3, PDF p. 12 (printed p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1644.pdf

import Mathlib
import Definitions.Def_PermSymQuery_Quadratic_Model
import Definitions.Def_PermSymQuery_Quadratic_Sampled

namespace PermSymQuery.Quadratic

/-- Lemma 3.3, PDF p.12 (printed p.10): isometry and every one-query bound. -/
theorem lemma_3_3 {N s q : ℕ} (hq : 1 ≤ q) (hs : q + 1 < s) (hsN : s < N)
    (hN : 3 * q + 2 ≤ N) :
    (∀ ψ ∈ CompPermOracle.Hle N (q + 1), ‖sampledW N s ψ‖ = ‖ψ‖) ∧
    ∀ (i : Fin N) (t : ℕ), t ≤ q →
      ‖((hatO (s := s) i).comp
            (CompPermOracle.opTensor (1 : CompPermOracle.Hil (CompPermOracle.Ans N) →L[ℂ]
              CompPermOracle.Hil (CompPermOracle.Ans N)) (sampledW N s)) -
          (CompPermOracle.opTensor (1 : CompPermOracle.Hil (CompPermOracle.Ans N) →L[ℂ]
            CompPermOracle.Hil (CompPermOracle.Ans N)) (sampledW N s)).comp
              (CompPermOracle.purP i)).comp
        (CompPermOracle.opTensor (1 : CompPermOracle.Hil (CompPermOracle.Ans N) →L[ℂ]
          CompPermOracle.Hil (CompPermOracle.Ans N)) (CompPermOracle.ProjLe N t))‖ ≤ eta N s q := by sorry

end PermSymQuery.Quadratic
