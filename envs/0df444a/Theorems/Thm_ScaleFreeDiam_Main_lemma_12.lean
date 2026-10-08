-- Prove2me | Theorems.Thm_ScaleFreeDiam_Main_lemma_12
-- name    : ScaleFreeDiam.Main.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:11:54.349913+00:00
-- url     : https://prove2.me/theorems/d1055db0-3a50-4215-af59-38cba50af07b
-- title:
--   Lemma 12, p. 24 — a sequence with f₀ ≥ (log n)²/n and growth (11) reaches (log n)²/√n within K = (1/2+ε) log n/log log n − 1 steps
-- statement:
--   Let $\varepsilon>0$ and set $K=(1/2+\varepsilon)\log n/\log\log n-1$. Let $a,b$ be as in the definitions file ($2^a$ the smallest power of $2$ above $(\log n)^7$, $2^b$ the largest below $2n/3$). Then, provided $n$ is sufficiently large, every real sequence $f_0,f_1,\dots$ with $f_0\ge(\log n)^2/n$ and
--   $$
--   f_{k+1}\ge\min\Big\{2\log_2\Big(\frac{f_kn}{\log n}\Big)-31,\ b-a-1\Big\}\frac{f_k}{1000}\qquad(k\ge0)
--   $$
--   has some index $k\le K$ with
--   $$
--   f_k\ge\frac{(\log n)^2}{\sqrt n}.
--   $$
--   This is the deterministic growth estimate behind the $(1/2+\varepsilon)\log n/\log\log n$ bound of Lemma 11.
--
--   **Formalization Note** The page says that $\ell=\min\{k: f_k\ge(\log n)^2/\sqrt n\}$ exists and is at most $K$; this is equivalent to the existence of some $k\le K$ with $f_k\ge(\log n)^2/\sqrt n$, which is how it is stated. "Provided $n$ is sufficiently large" is $\exists N_0\ \forall n\ge N_0\ \forall f$, with $N_0$ depending on $\varepsilon$ only.
-- source:
--   Bollobás and Riordan, The diameter of a scale-free random graph, Combinatorica 24 (2004), p. 24, Lemma 12, (11)

import Mathlib
import Definitions.Def_ScaleFreeDiam_Main_Process
import Definitions.Def_ScaleFreeDiam_Main_EndpointModel

namespace ScaleFreeDiam.Main

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical

theorem lemma_12 (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ f : ℕ → ℝ,
      (Real.log n) ^ 2 / n ≤ f 0 →
      (∀ k : ℕ, min (2 * Real.logb 2 (f k * n / Real.log n) - 31)
          ((bE n : ℝ) - aE n - 1) * f k / 1000 ≤ f (k + 1)) →
      ∃ k : ℕ, (k : ℝ) ≤ (1 / 2 + ε) * Real.log n / Real.log (Real.log n) - 1 ∧
        (Real.log n) ^ 2 / Real.sqrt n ≤ f k := by sorry

end ScaleFreeDiam.Main
