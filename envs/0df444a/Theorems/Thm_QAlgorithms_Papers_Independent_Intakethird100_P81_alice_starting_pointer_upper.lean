-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P81_alice_starting_pointer_upper
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P81.alice_starting_pointer_upper
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:03:39.046644+00:00
-- url     : https://prove2.me/theorems/46e14ea3-543d-4b13-990f-03a8509e6ee7
-- title:
--   Alice-starting exact pointer jumping
-- statement:
--   Let $n\ge2$ and $k\ge1$. Alice and Bob have unrestricted pointer maps on two disjoint sets of $n$ labelled vertices, and $v_1$ is a fixed Alice vertex independent of the inputs. Let $g_k$ be the endpoint after $k+1$ pointer applications. There is an absolute $C>0$, chosen before $k,n,v_1$, and an Alice-starting protocol with at most $k$ messages which is correct on every input with probability one and has worst-case bit cost
--   $$
--   c\le Ck\log_2 n.
--   $$
--
--   The output is the whole endpoint, so its bit parity is available locally as well. The last pointer application is local to the receiver after the $k$ charged messages; announcing the answer is uncharged. The public-mixture representation includes a deterministic protocol as a single seed.
-- source:
--   On rounds in quantum communication, arXiv:quant-ph/0004100v5, PDF p. 1, Abstract; Definition 11 on PDF p.12

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P81

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intakethird100.P81

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

open QAlgorithms.Papers.Independent.Bridge50.P44 (ClassicalFirst)

/-- Abstract p.1 and Definition 11 p.12: Alice starts, with exact endpoint output after
k+1 evaluations; the final receiver performs the last evaluation locally. -/
theorem alice_starting_pointer_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ (k n : ℕ), 0 < k → 2 ≤ n → ∀ v1 : Fin n,
      ∃ (c : ℕ) (P : PublicProtocol (PointerMap n) (PointerMap n) (Vertex n)),
        P.bounded .alice k c ∧ P.computes (endpoint k v1) 0 ∧
        (c : ℝ) ≤ C * k * Real.logb 2 n := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P81

end
