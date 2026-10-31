-- Prove2me | Theorems.Thm_StaticProphetSec_lemma_13
-- name    : StaticProphetSec.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:09:33.687976+00:00
-- url     : https://prove2.me/theorems/9098c7fa-77a4-4ccc-8684-d6b4db58e600
-- title:
--   Lemma 13 — support, log-concavity, unimodality and (38) for Poisson binomial laws
-- statement:
--   Fix $p\in[0,1]^n$ and let $\lambda=\sum_{i=1}^np_i$. Let $D_p$ be the sum of independent Bernoulli variables with means $p_i$, and for $j\in\mathbb N_0$ let $h_j=\mathbb P(D_p=j)$ and $H_j=\mathbb P(D_p\le j)$. Then:
--
--   1. The support $\{j:h_j>0\}$ is an interval.
--   2. $h$ is log-concave: for all $j\ge1$, $h_j^2\ge h_{j-1}h_{j+1}$, and this inequality is strict whenever $h_j>0$.
--   3. $h$ is unimodal with mode in $\{\lfloor\lambda\rfloor,\lceil\lambda\rceil\}$: $h_0\le h_1\le\dots\le h_{\lfloor\lambda\rfloor}$ and $h_{\lceil\lambda\rceil}\ge h_{\lceil\lambda\rceil+1}\ge\cdots$.
--   4. For any $j\ge2$,
--
--   $$H_{j-2}h_{j-1}\le H_{j-1}h_{j-2}.$$
--
--   These classical facts about Poisson binomial laws enter the sign analysis in the proof of Lemma 2.
--
--   Differences from the source:
--
--   - generalization: $n\in\mathbb N$ positive → $n\ge0$; reason: the proof of Lemma 2 uses $n-2$ variables, which is $0$ at $n=2$; at $n=0$ the claims are about the point mass at $0$
--   - encoding: $j\ge1$ in part 2 and $j\ge2$ in part 4 → shifted indices $j+1$ and $j+2$ with $j\ge0$; the chains of part 3 by consecutive terms; reason: avoids natural-number subtraction; same instances
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, Lemma 13, p.36

import Mathlib
import Definitions.Def_CommitteeVoting_SingleVoter_PoissonBinomial

open CommitteeVoting.SingleVoter (pbPMF pbCDF)

namespace StaticProphetSec

/-- Lemma 13 (Arnosti & Ma, arXiv:2108.12893v2, Lemma 13, p.36). Let `D_p` be the sum of
independent Bernoulli variables with means `p_1, …, p_n`, `λ = ∑ i, p_i`, `h_j = P(D_p = j)` and
`H_j = P(D_p ≤ j)`. Then (1) the support of `h` is an interval; (2) `h` is log-concave, strictly
wherever `h_j > 0`; (3) `h` increases up to `⌊λ⌋` and decreases from `⌈λ⌉` on; (4)
`H_{j-2} h_{j-1} ≤ H_{j-1} h_{j-2}` for `j ≥ 2`, inequality (38).

**Formalization Note.** The indices are shifted to avoid natural-number subtraction: part 2 is
stated at `j + 1` for `j ≥ 0`, part 4 at `j + 2` for `j ≥ 0`. The chains of part 3 are stated by
consecutive terms. `n = 0` is allowed (the empty sum, `h_0 = 1`): the proof of Lemma 2 applies
this lemma to `n - 2` variables, which is `0` at `n = 2`. -/
theorem lemma_13 {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    Set.OrdConnected {j : ℕ | 0 < pbPMF p Finset.univ j} ∧
    (∀ j : ℕ, pbPMF p Finset.univ j * pbPMF p Finset.univ (j + 2)
        ≤ pbPMF p Finset.univ (j + 1) ^ 2 ∧
      (0 < pbPMF p Finset.univ (j + 1) →
        pbPMF p Finset.univ j * pbPMF p Finset.univ (j + 2)
          < pbPMF p Finset.univ (j + 1) ^ 2)) ∧
    ((∀ j : ℕ, j < ⌊∑ i, p i⌋₊ → pbPMF p Finset.univ j ≤ pbPMF p Finset.univ (j + 1)) ∧
      (∀ j : ℕ, ⌈∑ i, p i⌉₊ ≤ j → pbPMF p Finset.univ (j + 1) ≤ pbPMF p Finset.univ j)) ∧
    (∀ j : ℕ, pbCDF p Finset.univ j * pbPMF p Finset.univ (j + 1)
        ≤ pbCDF p Finset.univ (j + 1) * pbPMF p Finset.univ j) := by sorry

end StaticProphetSec
