-- Prove2me | Theorems.Thm_QubitFreqSensing_lemma_5_12
-- name    : QubitFreqSensing.lemma_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:10.599315+00:00
-- url     : https://prove2.me/theorems/a5bbce3a-96b1-4a7c-9f79-36b0646df2f0
-- title:
--   Lemma 5.12 — the rounding $R_K(h)$ is $\pm1$-valued, has $\le2K$ pieces and errs by $\le LT^2/(2K)$ against $L$-Lipschitz tests
-- statement:
--   Let $T>0$, $K\ge1$ and let $h:[0,T]\to[-1,1]$ be measurable. Partition $[0,T]$ into $K$ intervals $I=[a,a+\delta]$ of length $\delta=T/K$, let $p_I=\bigl(\delta+\int_I h(t)\,dt\bigr)/2$, and let $R_K(h)$ be $+1$ on $[a,a+p_I)$ and $-1$ on $[a+p_I,a+\delta)$, with the left limiting sign at $T$. Then:
--
--   1. $R_K(h)(t)\in\{-1,1\}$ for every $t\in[0,T]$;
--   2. $R_K(h)$ has at most $2K$ constant pieces;
--   3. for every $L\ge0$ and every function $g$ that is $L$-Lipschitz on $[0,T]$,
--   $$
--   \left|\int_0^T\bigl(R_K(h)-h\bigr)(t)\,g(t)\,dt\right|\ \le\ \frac{LT^2}{2K}. \tag{15}
--   $$
--
--   Applied with $g(t)=\cos(\omega_i t)$, which is $\omega_i$-Lipschitz, this turns the real parts and imaginary parts of the function of Theorem 5.1 into the $\pm1$ patterns of Theorem 5.13.
--
--   Differences from the source:
--   - reading: partition [0, T] into K equal intervals of length δ = T/K → T > 0 and K ≥ 1; reason: implicit in the partition
--   - encoding: R_K(h) given by cases with half-open intervals and the left limiting sign at T → the function roundK T K h; reason: the same values on [0, T]; values outside [0, T] play no role
--   - encoding: at most 2K constant pieces → HasConstPieces with n ≤ 2K pieces (monotone breakpoints, empty pieces allowed); reason: 'at most'
--   - encoding: h : [0, T] → [−1, 1] measurable → h : ℝ → ℝ Measurable with h t ∈ [−1, 1] for t ∈ [0, T]; reason: a measurable h on [0, T] extends measurably by 0; roundK and every integral only read h on [0, T]
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), Lemma 5.12, p.22 (PDF p.22)

import Mathlib
import Definitions.Def_QubitFreqSensing_SignPattern

namespace QubitFreqSensing

/-- **Lemma 5.12** (Chen, Coladangelo, Li, Zhang, manuscript (STOC 2027 submission), Lemma 5.12,
p.22). "Let h : [0, T] → [−1, 1] be measurable, and partition [0, T] into K equal intervals of
length δ = T/K. For each interval I = [a, a + δ], let pI := (δ + ∫_I h(t) dt)/2,
RK(h)(t) := +1 if a ≤ t < a + pI, −1 if a + pI ≤ t < a + δ. Use half-open intervals and the left
limiting sign at T. This gives a function taking values in {−1, 1} everywhere, with at most 2K
constant pieces. For any real L-Lipschitz function g on [0, T], |∫_0^T (RK(h) − h) g(t) dt| ≤
LT²/(2K). (15)"

Three clauses: `R_K(h)` takes values in `{−1, 1}` on `[0, T]`; it has at most `2K` constant pieces;
and (15) holds for every `L ≥ 0` and every `g` that is `L`-Lipschitz on `[0, T]`.

**Formalization Note** `R_K(h)` is the function `roundK T K h`. `T > 0` and `K ≥ 1` are implicit
in "K equal intervals of length δ = T/K". -/
theorem lemma_5_12 (T : ℝ) (hT : 0 < T) (K : ℕ) (hK : 1 ≤ K) (h : ℝ → ℝ) (hh : Measurable h)
    (hrange : ∀ t ∈ Set.Icc 0 T, h t ∈ Set.Icc (-1 : ℝ) 1) :
    (∀ t ∈ Set.Icc 0 T, roundK T K h t = 1 ∨ roundK T K h t = -1) ∧
    (∃ n : ℕ, n ≤ 2 * K ∧ HasConstPieces T (roundK T K h) n) ∧
    (∀ (L : NNReal) (g : ℝ → ℝ), LipschitzOnWith L g (Set.Icc 0 T) →
      |∫ t in (0 : ℝ)..T, (roundK T K h t - h t) * g t| ≤ L * T ^ 2 / (2 * K)) := by sorry

end QubitFreqSensing
