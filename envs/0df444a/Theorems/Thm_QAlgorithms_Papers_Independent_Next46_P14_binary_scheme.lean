-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P14_binary_scheme
-- name    : QAlgorithms.Papers.Independent.Next46.P14.binary_scheme
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:12:59.22192+00:00
-- url     : https://prove2.me/theorems/97b513b9-3e52-4060-86ee-d5e1d75d9182
-- title:
--   Explicit binary query-flip SPIR scheme
-- statement:
--   Let $K,N\geq2$. Let the requested index be independently uniform on the K messages. Over $\mathbb F_2$, let each message $W_j=(x_{j,i})_{i=1}^{N-1}$ and the user array $h=(h_{j,i})$ be independent uniform arrays, and let S be an independent uniform bit. Server 1 receives $q_1=h$; server $i+1$ receives $q_{i+1}=h+e_{k,i}$. Each server uses its own received-query argument in the encoder
--
--   $$A_n(q_n,W,S)=\sum_{j=1}^K\sum_{i=1}^{N-1}(q_n)_{j,i}x_{j,i}+S.$$
--
--   Then $A_{i+1}-A_1=x_{k,i}$ for every realization. Every full server view $(q_n,A_n,W,S)$ has the same law for all requests. For each k, the joint undesired-message vector is independent of $(q_{1:N},A_{1:N},h)$. Exactly N one-bit answers are downloaded and one shared random bit is used, giving
--
--   $$R=1-1/N,\qquad H_2(S)/(N-1)=1/(N-1).$$
--
--   This is the source’s classical noiseless achievable scheme.
--
--   For every positive integer r there is an exact-private, zero-error binary protocol with each message of length r(N−1), total download rN and shared entropy r bits. Every requested message has rate 1−1/N. This is the source’s positive-multiple attainment assertion, obtained by independent repetitions.
-- source:
--   The Capacity of Symmetric Private Information Retrieval, arXiv:1606.08828v2, PDF p. 7, §4.1.1, (17)–(24); §3.1 Observation 5 (PDF p.6)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P14

noncomputable section

open scoped BigOperators ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P14

/-- Section 4.1.1, PDF pp.7–8, (17)–(24): the specified binary scheme has exact
correctness, both FULL-VIEW privacy properties, N downloaded bits, and one shared
random bit. Its rate and normalized randomness are exactly the stated values.
Observation 5, PDF p.6, also gives zero-error attainment at every positive
multiple of N−1 bits, with r shared bits and rN downloaded bits. -/
theorem binary_scheme (K N : ℕ) (hK : 2 ≤ K) (hN : 2 ≤ N) :
    (∀ (k : Fin K) (w h : BinaryArray K N) (s : ZMod 2) (i : Fin (N - 1)),
      binaryAnswer (binaryQuery k (⟨i.val + 1, by omega⟩ : Fin N) h) w s -
        binaryAnswer (binaryQuery k (⟨0, by omega⟩ : Fin N) h) w s = w k i) ∧
    (∀ (k k2 : Fin K) (n : Fin N),
      (spirBinaryLaw K N).map (binaryServerView k n) =
        (spirBinaryLaw K N).map (binaryServerView k2 n)) ∧
    (∀ k : Fin K, Independent (spirBinaryLaw K N) (binaryUndesired k) (binaryUserView k)) ∧
    binaryDownload N = N ∧
    spirEntropy 2 (PMF.uniformOfFintype (ZMod 2)) = 1 ∧
    ((N - 1 : ℕ) : ℝ) / (binaryDownload N : ℝ) = 1 - 1 / (N : ℝ) ∧
    spirEntropy 2 (PMF.uniformOfFintype (ZMod 2)) / ((N - 1 : ℕ) : ℝ≥0∞) =
      ENNReal.ofReal (1 / ((N : ℝ) - 1)) ∧
    (∀ r : ℕ, 0 < r →
      ∃ b : SpirProtocol
        (equalParameters 2 Nat.prime_two K N (by omega) (by omega)) (r * (N - 1)),
        Private b ∧ ZeroError b ∧ b.download = r * N ∧
          spirEntropy 2 b.sharedSeed = (r : ℝ≥0∞) ∧
          ∀ k, spirRate b k = 1 - 1 / (N : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P14

end
