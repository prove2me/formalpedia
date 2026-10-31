-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P41_recycling_leakage_attack
-- name    : QAlgorithms.Papers.Independent.Intake100.P41.recycling_leakage_attack
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:20:26.410102+00:00
-- url     : https://prove2.me/theorems/857824e5-4880-4cde-b4ec-9d89e422e750
-- title:
--   One feedback attack witnesses corruption and hash-key entropy leakage
-- statement:
--   Let $K$ be finite and nonempty, let $X$ contain at least two messages, let $T=\{0,1\}^m$, and suppose $h:K\times X\to T$ is $1/|T|$-AXU$_2$. Choose the hash key uniformly once and use an independent perfect uniform pad for every authentication round. Suppose $1\le n\le |T|$. Eve chooses the honest messages, intercepts each valid tagged message, substitutes a pair, and learns its verification result before the next round. There is one attack, chosen independently of the secret key and pads, such that
--
--   $$
--   \Pr[\text{at least one changed message is accepted in rounds }1,\ldots,n]\ge\frac{n}{|T|},
--   $$
--
--   and, for that same attack,
--
--   $$
--   H(K\mid Z_n)\le\log_2\frac{|K|}{|T|}+\left(1-\frac{n}{|T|}\right)\log_2(|T|-n).
--   $$
--
--   The transcript $Z_n$ contains the honest and substituted messages, original and substituted tags, and all acceptance or rejection bits; the attack's fixed public choices are implicit constants. Entropy is Shannon entropy in bits of the retained hash key alone. At $n=|T|$ the second summand is interpreted as zero. The result shows leakage sufficient for certain forgery at saturation, while the residual key entropy can remain $\log_2(|K|/|T|)$.
--
--   **Formalization Note** Conditional entropy is computed by averaging posterior-key entropy over the finite uniform key-and-pad sample space; no finite-message assumption is needed.
-- source:
--   Key recycling in authentication, arXiv:1202.1229v3, PDF p. 16, Theorem 8

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P41

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P41

open QAlgorithms.Papers.Independent.Bridge50.P44 (xorWord verifyTag)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.16--17, Theorem 8: one attack witnesses both the n/|T| success lower
bound and the conditional hash-key entropy upper bound. The full public trace
includes both tags and all verification feedback. The endpoint n = |T| is kept;
its residual entropy is log2(|K|/|T|), not necessarily zero. -/
theorem recycling_leakage_attack {K X : Type*} [Fintype K] [Nonempty K]
    [Nontrivial X] {m n : ℕ} (hn : 1 ≤ n) (hnmax : n ≤ Fintype.card (Tag m))
    (h : K → X → Tag m) (hh : IsAXU2 h (1 / (Fintype.card (Tag m) : ℝ))) :
    ∃ a : AdaptiveAttack X (Tag m),
      (n : ℝ) / (Fintype.card (Tag m) : ℝ) ≤
        uniformProbability (fun seed : K × (Fin n → Tag m) =>
          corrupts (attackTrace h a seed.1 seed.2)) ∧
      conditionalKeyEntropy (fun seed : K × (Fin n → Tag m) =>
        attackTrace h a seed.1 seed.2) ≤ leakageBound K m n := by sorry

end QAlgorithms.Papers.Independent.Intake100.P41

end
