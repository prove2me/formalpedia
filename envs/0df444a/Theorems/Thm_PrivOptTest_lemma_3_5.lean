-- Prove2me | Theorems.Thm_PrivOptTest_lemma_3_5
-- name    : PrivOptTest.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:59:37.514624+00:00
-- url     : https://prove2.me/theorems/c5aeaec4-01d5-4d45-825e-658b687e8ce6
-- title:
--   Lemma 3.5, p.16 — lifting preserves the loss and orders the extremal blocks
-- statement:
--   Let $\psi_A(x)=2x+1$ and $\psi_B(x)=2x$ (append the bit $1$, resp. $0$, to a binary string). Let $S_A,S_B$ be datasets of size $n$ of natural numbers, $1\le k\le n$, and $\tilde S_A=\psi_A(S_A)$, $\tilde S_B=\psi_B(S_B)$. Then
--   $$\mathrm{opt}_{\mathcal H_{\mathrm{thr}}}(\tilde S_A,\tilde S_B)=\mathrm{opt}_{\mathcal H_{\mathrm{thr}}}(S_A,S_B),$$
--   and
--   1. if $\mathrm{opt}_{\mathcal H_{\mathrm{thr}}}(S_A,S_B)=0$, every element of $\tilde S^{\uparrow}_{A,k}$ is below every element of $\tilde S^{\downarrow}_{B,k}$;
--   2. if $\mathrm{opt}_{\mathcal H_{\mathrm{thr}}}(S_A,S_B)\ge2k-1$, every element of $\tilde S^{\uparrow}_{A,k}$ is above every element of $\tilde S^{\downarrow}_{B,k}$.
--
--   The lemma reduces the testing promise to a strict comparison between two blocks of $k$ records.
--
--   Differences from the source:
--   - generalization: records in X = {0,1}^b with m = 2^b → any natural numbers; reason: the proof reads strings as integers and uses only order and parity; b-bit strings are the numbers below 2^b
--   - encoding: multisets of size n, max S̃↑ < min S̃↓ → sequences Fin n → ℕ; every element of one sorted block below every element of the other; reason: opt and blocks depend only on the multiset; the two forms agree on nonempty blocks (k ≥ 1)
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Lemma 3.5, p.16

import Mathlib
import Definitions.Def_PrivOptTest_IsTester
import Definitions.Def_PrivOptTest_Trie

namespace PrivOptTest

/-- **Lemma 3.5** (p.16). Lifting records by `ψ_A(x) = x∥1 = 2x + 1` and `ψ_B(x) = x∥0 = 2x` does not
change the threshold loss; if the instance is realizable, Alice's `k` largest lifted records lie below
Bob's `k` smallest; if its loss is at least `2k − 1`, they lie above.
Source: Haghifam, Patel, Blum, Fanti, Ziani, *Should We Combine Our Data?*, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Lemma 3.5, p.16.

**Formalization Note.** Records are natural numbers (`b`-bit strings read as integers, as in the
proof), of any size. `max S̃↑_{A,k} < min S̃↓_{B,k}` is `MatchOrder`: every element of the first block is
below every element of the second, equivalent since both blocks are nonempty for `1 ≤ k`. -/
theorem lemma_3_5 {n : ℕ} (SA SB : Fin n → ℕ) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    opt Hthr (fun i => ((psiA (SA i) : ℕ) : ℝ)) (fun i => ((psiB (SB i) : ℕ) : ℝ)) =
        opt Hthr (fun i => ((SA i : ℕ) : ℝ)) (fun i => ((SB i : ℕ) : ℝ)) ∧
      (opt Hthr (fun i => ((SA i : ℕ) : ℝ)) (fun i => ((SB i : ℕ) : ℝ)) = 0 →
        MatchOrder (blockUp k fun i => psiA (SA i)) (blockDown k fun i => psiB (SB i))) ∧
      (2 * k - 1 ≤ opt Hthr (fun i => ((SA i : ℕ) : ℝ)) (fun i => ((SB i : ℕ) : ℝ)) →
        FarOrder (blockUp k fun i => psiA (SA i)) (blockDown k fun i => psiB (SB i))) := by sorry

end PrivOptTest
