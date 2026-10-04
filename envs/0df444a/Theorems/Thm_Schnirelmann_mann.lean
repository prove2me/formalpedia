-- Prove2me | Theorems.Thm_Schnirelmann_mann
-- name    : Schnirelmann.mann
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T06:01:27.625011+00:00
-- url     : https://prove2.me/theorems/e1aeaed9-e852-439b-9d4c-9f3c360502a1
-- title:
--   Mann's $\alpha+\beta$ theorem: $\sigma(D+E)\ge\min(1,\sigma(D)+\sigma(E))$
-- statement:
--   **Mann's $\alpha+\beta$ theorem.** For a set $A\subseteq\mathbb{N}$ write $A(n)=\lvert A\cap[1,n]\rvert$ and let
--   $$\sigma(A)=\inf_{n\ge 1}\frac{A(n)}{n}$$
--   be its Schnirelmann density. Let $D,E\subseteq\mathbb{N}$ be sets that both contain $0$, and let $D+E=\{d+e : d\in D,\ e\in E\}$ be their sumset. Then
--   $$\sigma(D+E)\ \ge\ \min\bigl(1,\ \sigma(D)+\sigma(E)\bigr).$$
--
--   This is the $\alpha+\beta$ conjecture (Khinchin; Landau and Schnirelmann), proved by H. B. Mann in 1942. It strengthens Schnirelmann's inequality $\sigma(D+E)\ge\sigma(D)+\sigma(E)-\sigma(D)\sigma(E)$ by removing the product term, and it contains Schnirelmann's lemma ($\sigma(D)+\sigma(E)\ge 1$ implies $D+E=\mathbb{N}$) as the case $\min=1$.
--
--   A standard consequence, by induction on $h$, is $\sigma(hA)\ge\min(1,\,h\,\sigma(A))$ for every $A$ containing $0$. In particular a set with $\sigma(A)>0$ and $0\in A$ is an additive basis of order at most $\lceil 1/\sigma(A)\rceil$, instead of the order of size about $\ln 2/\sigma(A)$ that the product inequality gives. This is the quantitative input that sharpens bounds of the form "every integer is a sum of at most $k$ primes" obtained from a lower bound for the density of the set of sums of two primes.
--
--   **Formalization note.** `schnirelmannDensity` is Mathlib's definition (it counts elements of $A$ in $\{1,\dots,n\}$, so membership of $0$ does not affect the density). The sumset is the pointwise sum on `Set ℕ`. The hypotheses $0\in D$ and $0\in E$ are the standard ones in Mann's theorem.
-- source:
--   H. B. Mann, A proof of the fundamental theorem on the density of sums of sets of positive integers, Ann. of Math. 43 (1942), 523-527; see M. B. Nathanson, Additive number theory and the Dyson transform, arXiv:2407.12253, Theorem 2 (Mann).

import Mathlib

namespace Schnirelmann

open Pointwise Classical in
theorem mann (D E : Set ℕ) (hD : 0 ∈ D) (hE : 0 ∈ E) :
    min 1 (schnirelmannDensity D + schnirelmannDensity E) ≤ schnirelmannDensity (D + E) := by
  sorry

end Schnirelmann
