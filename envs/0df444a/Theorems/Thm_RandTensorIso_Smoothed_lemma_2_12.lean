-- Prove2me | Theorems.Thm_RandTensorIso_Smoothed_lemma_2_12
-- name    : RandTensorIso.Smoothed.lemma_2_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:38:04.894675+00:00
-- url     : https://prove2.me/theorems/820f105b-bd72-4474-aebc-5865f9db843b
-- title:
--   Lemma 2.12 — density conditions force a $(\tau,5)$-seed
-- statement:
--   Let $n\ge2$, $S\in\mathbb C^{n\times n\times n}$, $\tau>0$, $\beta\in(0,1/4]$, and let $r\ge1$ be an integer with $r\le n-\beta n+1$. Suppose that
--   (i) $|\{p\in[n]^3:|S(p)|\ge\tau\}|\ge4\beta n^3$;
--   (ii) for every $d\in[3]$ and all $J,K\subseteq[n]$ with $|J|,|K|\ge\beta n$, fewer than $r$ indices $x\in[n]$ satisfy $|S(p)|<\tau$ for every $p\in\mathrm{Rect}_d(x;J,K)$;
--   (iii) for every $d\in[3]$, every $x\in[n]$ and all $J,K\subseteq[n]$ with $|J|,|K|\ge n-r+1$,
--   $$\sum_{p\in\mathrm{Rect}_d(x;J,K)}|S(p)|^2\ge\tau^2.$$
--   Then $S$ has a $(\tau,5)$-seed. This is the deterministic half of the argument that random cores have seeds; Lemma 2.13 supplies (i)–(iii).
--
--   Differences from the source: none.
-- source:
--   Chizewer, Everett, Mithal, Qiao, Random tensor isomorphism under orthogonal and unitary actions: Smoothed and average-case analysis, STOC 2027 submission (manuscript sha256 f4a12b77…), p. 28 (PDF 30), Lemma 2.12

import Mathlib
import Definitions.Def_RandTensorIso_Smoothed_Tensor
import Definitions.Def_RandTensorIso_Smoothed_Spectral
import Definitions.Def_RandTensorIso_Smoothed_Seed

open scoped Classical

namespace RandTensorIso.Smoothed

/-- Lemma 2.12 (p. 28). Density conditions (i)–(iii) force a `(τ, 5)`-seed. -/
theorem lemma_2_12 (n : ℕ) (S : Tensor3 n) (τ β : ℝ) (r : ℕ)
    (hn : 2 ≤ n) (hτ : 0 < τ) (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4)
    (hr1 : 1 ≤ r) (hrn : (r : ℝ) ≤ n - β * n + 1)
    (hi : 4 * β * (n : ℝ) ^ 3 ≤ (Finset.univ.filter (fun p => τ ≤ ‖S p‖)).card)
    (hii : ∀ (d : Fin 3) (J K : Finset (Fin n)), β * n ≤ J.card → β * n ≤ K.card →
      (Finset.univ.filter (fun x : Fin n => ∀ a ∈ J, ∀ b ∈ K, ‖S (pos d x a b)‖ < τ)).card < r)
    (hiii : ∀ (d : Fin 3) (x : Fin n) (J K : Finset (Fin n)),
      (n : ℝ) - r + 1 ≤ J.card → (n : ℝ) - r + 1 ≤ K.card →
      τ ^ 2 ≤ rectWeight S d x J K) :
    HasSeed S τ 5 := by sorry

end RandTensorIso.Smoothed
