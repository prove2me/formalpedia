-- Prove2me | Theorems.Thm_TaoFivePrimes_vinogradov_lemma_if_form_from_block
-- name    : TaoFivePrimes.vinogradov_lemma_if_form_from_block
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T18:46:50.674925+00:00
-- url     : https://prove2.me/theorems/90cf0471-25c3-46c9-96da-43e5dbc95ea8
-- title:
--   Tao Lemma 3.4: subdivision into blocks of length q
-- statement:
--   **Subdividing the Vinogradov-type lemma.** Let $q\ge1$, $A',B\ge0$, $\theta'\in\mathbb R$ and $u<v$, and suppose the single-block estimate
--
--   $$\sum_{m<n\le m+q}\min\Bigl(A',\frac B{|\sin(\pi\alpha'n+\theta')|}\Bigr)\le2A'+\frac2\pi Bq\log4q$$
--
--   holds for every integer $m$ (a term with vanishing sine contributing $A'$). Then
--
--   $$\sum_{\lfloor u\rfloor<n\le\lfloor v\rfloor}\min\Bigl(A',\frac B{|\sin(\pi\alpha'n+\theta')|}\Bigr)\ \le\ \Bigl(\Bigl\lfloor\frac{v-u}q\Bigr\rfloor+1\Bigr)\Bigl(2A'+\frac2\pi Bq\log4q\Bigr).$$
--
--   This is the subdivision half of the source's Lemma 3.4, separated from the block estimate it quotes. The summand is nonnegative, so it is enough to cover $(\lfloor u\rfloor,\lfloor v\rfloor]$ by $K=\lfloor\frac{v-u}{q}\rfloor+1$ consecutive blocks of length $q$ starting at $\lfloor u\rfloor$ and add the block estimate $K$ times. The covering is exactly tight: $Kq>v-u$ by the definition of the floor, while $\lfloor v\rfloor-\lfloor u\rfloor<v-u+1$, and both $Kq$ and $\lfloor v\rfloor-\lfloor u\rfloor$ are integers, so $\lfloor v\rfloor\le\lfloor u\rfloor+Kq$.
--
--   **Formalization Note** The rational approximation to $\alpha'$ plays no role here — it is used only inside the block estimate — so it does not appear among the hypotheses. The induction over blocks is on $K$, splitting $(\lfloor u\rfloor,\lfloor u\rfloor+(k+1)q]$ as a disjoint union of $(\lfloor u\rfloor,\lfloor u\rfloor+kq]$ and one further block.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 3, Lemma 3.4 (Vinogradov-type lemma), the subdivision of the interval into blocks of length q

import Mathlib

open Finset

theorem TaoFivePrimes.vinogradov_lemma_if_form_from_block
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q)
    (A' alpha' theta' u v : ℝ) (hA' : 0 ≤ A') (huv : u < v)
    (hblock : ∀ m : ℤ,
      (∑ n ∈ Finset.Ioc m (m + (q : ℤ)),
          (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
            else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
        ≤ 2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) :
    (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
        (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
          else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
      ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
          * (2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) := by sorry
