-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_long_chains
-- name    : SingleCopyMoments.Adaptive.long_chains
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:49:34.309201+00:00
-- url     : https://prove2.me/theorems/71dbb21d-8d97-47e6-a397-1d8dbd80d470
-- title:
--   Lemma 38 — Deterministic bound for long chains
-- statement:
--   For any realization whose every subset sum has operator norm at most $K$, and every integer $\ell\ge1$, the ordered distinct-index chain and its complex trace satisfy
--
--   $$\|A_{\ell,N}\|_{op}\le(6K)^\ell,\qquad|C_{\ell,N}|\le d(6K)^\ell.$$
--
--   The statement is deterministic, retains the exact factor $6$, and includes all degrees, even when $\ell>N$ so that the distinct-index sum is zero. It controls the full long-degree tail rather than only a fixed-order truncation.
--
--   Differences from the source:
--   - encoding: ordered distinct-index products → a sum over embeddings Fin ell into Fin N, with list products in their given order; reason: there is one term for each ordered distinct tuple; complex multiplication order is preserved
--   - generalization: the retained matrices of Lemma 35 with K=2(kappa+2) → any complex matrices and any nonnegative K bounding every subset sum; reason: the source proof is deterministic and uses only that bound; its retained matrices and positive K are included
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Lemma 38, (7.35), printed p. 42 (PDF p. 44); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf; PDF SHA-256 f19fd65f41a444a79243fa55aab5dfca3db6adb571b06acff78ee49932174fa9.

import Definitions.Def_SingleCopyMoments_Adaptive_Records

namespace SingleCopyMoments.Adaptive

/-- Lemma 38, printed pp.42–43 (PDF pp.44–45), deterministic (7.26) is its premise. -/
theorem long_chains (d N : ℕ) (hd : 0 < d) (Y : Fin N → Op d) (K : ℝ)
    (hK : 0 ≤ K) (subsets : ∀ J : Finset (Fin N), opNorm (∑ i ∈ J, Y i) ≤ K)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    opNorm (chain Y ℓ) ≤ (6*K)^ℓ ∧ ‖cycle Y ℓ‖ ≤ (d : ℝ)*(6*K)^ℓ := by sorry

end SingleCopyMoments.Adaptive
