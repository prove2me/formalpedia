-- Prove2me | Theorems.Thm_ScaleFreeDiam_Main_lemma_7
-- name    : ScaleFreeDiam.Main.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:18.517597+00:00
-- url     : https://prove2.me/theorems/ea42d62e-0c7e-45d1-80d2-e30aae1c4ac3
-- title:
--   Lemma 7, pp. 16–17 — for m ≥ 2 each of E₁,…,E₅ has probability tending to 1
-- statement:
--   Fix $m\ge2$. Let $r_1,\dots,r_{mn}$ be independent $M_2(0,1)$ random variables (density $2x$ on $(0,1)$), $R_1\le\dots\le R_{mn}$ their sorted values, $W_i=R_{mi}$ ($1\le i\le n$), $W_0=0$ and $w_i=W_i-W_{i-1}$. With $s=2^a$, $b$ and $I_t$ as in the definitions file, each of the events
--   1. $E_1=\{|W_i-\sqrt{i/n}|\le\frac1{10}\sqrt{i/n}\ \text{for } s\le i\le n\}$,
--   2. $E_2=\{I_t \text{ contains at least } 2^{t-1}\text{ vertices } i \text{ with } w_i\ge 1/(10\sqrt{in}),\ a\le t<b\}$,
--   3. $E_3=\{w_1\ge 4/(\log n\sqrt n)\}$,
--   4. $E_4=\{w_i\ge(\log n)^2/n\ \text{for } i<n^{1/5}\}$,
--   5. $E_5=\{w_i\le n^{-4/5}\ \text{for } i>n/(\log n)^5\}$
--
--   has probability tending to $1$ as $n\to\infty$:
--   $$
--   \mathbb P(E_r^{c})\to0\qquad(r=1,\dots,5).
--   $$
--   The lemma says that the sorted right endpoints of a random pairing are, with high probability, spread as in the deterministic profile $W_i\approx\sqrt{i/n}$; the rest of the proof of the upper bound works conditionally on these events.
--
--   **Formalization Note** The statement is written as "the probability of the complement tends to $0$", the form in which it is proved; the law of $(r_1,\dots,r_{mn})$ is the product measure of $M_2(0,1)$.
-- source:
--   Bollobás and Riordan, The diameter of a scale-free random graph, Combinatorica 24 (2004), pp. 16–17, Lemma 7

import Mathlib
import Definitions.Def_ScaleFreeDiam_Main_Process
import Definitions.Def_ScaleFreeDiam_Main_EndpointModel

namespace ScaleFreeDiam.Main

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical

theorem lemma_7 (m : ℕ) (hm : 2 ≤ m) :
    Tendsto (fun n => Measure.pi (fun _ : Fin (m * n) => M2) {r | ¬ E1 n (Wof m n r)})
        atTop (𝓝 0) ∧
      Tendsto (fun n => Measure.pi (fun _ : Fin (m * n) => M2) {r | ¬ E2 n (Wof m n r)})
        atTop (𝓝 0) ∧
      Tendsto (fun n => Measure.pi (fun _ : Fin (m * n) => M2) {r | ¬ E3 n (Wof m n r)})
        atTop (𝓝 0) ∧
      Tendsto (fun n => Measure.pi (fun _ : Fin (m * n) => M2) {r | ¬ E4 n (Wof m n r)})
        atTop (𝓝 0) ∧
      Tendsto (fun n => Measure.pi (fun _ : Fin (m * n) => M2) {r | ¬ E5 n (Wof m n r)})
        atTop (𝓝 0) := by sorry

end ScaleFreeDiam.Main
