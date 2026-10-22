-- Prove2me | Theorems.Thm_TemperleyLieb_Gram_lemma_3_5
-- name    : TemperleyLieb.Gram.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:44.441988+00:00
-- url     : https://prove2.me/theorems/c95ea0b2-6deb-47e2-be78-43e2f0b93c9e
-- title:
--   Lemma 3.5, p. 14 — the central elements z_i act on m_{t^λ} by explicit scalars
-- statement:
--   Let $\lambda=(f,n-2f)$ be a partition of $n$, let $m_\lambda=e_1e_3\cdots e_{2f-1}$, and let $\check A^\lambda_n$ be the span of the Murphy elements $m_{\mathfrak u\mathfrak v}$ of the shapes $\mu\triangleright\lambda$. In the cell module $C^\lambda$ the generator $m_{\mathfrak t^\lambda}$ is the class $m_\lambda+\check A^\lambda_n$. For every integer $1\le i\le n$,
--
--   $$m_{\mathfrak t^\lambda}z_i=\begin{cases}p_fp_{i-f+1}\,m_{\mathfrak t^\lambda},&\text{if }2f+1\le i\le n,\\ p_kp_{i-k+1}\,m_{\mathfrak t^\lambda},&\text{if } i=2k\text{ or }i=2k+1,\ 0\le k\le f.\end{cases}$$
--
--   Here $z_i=\sum_{k=0}^i x^kT_{i-k}$ and $p_i$ are as in §3. This computes the eigenvalues of the central elements, from which the contents $r_{\mathfrak t}(k)$ are derived.
--
--   **Formalization Note** The congruence is stated in $A_n(x)$: $m_\lambda z_i-c\,m_\lambda$ lies in the span of the Murphy elements of shapes with more cups. The two cases agree when $i=2f+1$. The paper defines $\check A^\lambda_n$ as a sum of two-sided ideals; by the cellularity of the Murphy basis (Lemma 2.3) it equals this span, which is the convention of the cellular datum used throughout the mission.
-- source:
--   Enyang, Representations of Temperley–Lieb Algebras, arXiv:0710.3218v1, p. 14, Lemma 3.5; p. 2, definition of m_lambda and the ideals

import Mathlib
import Definitions.Def_TemperleyLieb_Gram_Models

namespace TemperleyLieb.Gram
open QAlgorithms.Papers.Independent.Support21.P08

/-- Enyang, Lemma 3.5, p. 14: the central element `z_i` acts on the generator
`m_{t^λ} = m_λ + Ǎ^λ_n` of the cell module by an explicit scalar. `Ǎ^λ_n` is the
span of the Murphy elements of the shapes with more cups. -/
theorem lemma_3_5 (n : ℕ) (f : Fin (n / 2 + 1)) (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    (2 * (f : ℕ) + 1 ≤ i →
      mLam R Polynomial.X n f * zJM R Polynomial.X n i -
          (p (f : ℕ) * p (i - (f : ℕ) + 1)) • mLam R Polynomial.X n f ∈
        higherSpan (R := R) (murphy R Polynomial.X n) f) ∧
    (∀ k : ℕ, k ≤ (f : ℕ) → (i = 2 * k ∨ i = 2 * k + 1) →
      mLam R Polynomial.X n f * zJM R Polynomial.X n i -
          (p k * p (i - k + 1)) • mLam R Polynomial.X n f ∈
        higherSpan (R := R) (murphy R Polynomial.X n) f) := by sorry

end TemperleyLieb.Gram
