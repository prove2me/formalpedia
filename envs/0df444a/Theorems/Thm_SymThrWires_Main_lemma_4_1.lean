-- Prove2me | Theorems.Thm_SymThrWires_Main_lemma_4_1
-- name    : SymThrWires.Main.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:16:57.129721+00:00
-- url     : https://prove2.me/theorems/421ea51a-c550-4226-b338-5b88edf5efe8
-- title:
--   Lemma 4.1 — E tr H(E_D)^{2m} ≤ 4N²((4QN³)^m m! + (8N²/3)^{2m}(2m)!) for entries in [−1, 1] and i.i.d. uniform samples
-- statement:
--   Let $m\ge1$, $N,Q\ge0$, let $D$ be a real $N\times N$ matrix with entries in $[-1,1]$, and let the $Q$ sample pairs $(U_t,V_t)$ be independent and uniform on $[N]^2$. With the error matrix $E_D$ and the dilation $H(E)=\begin{pmatrix}0&E\\E^{\mathsf T}&0\end{pmatrix}$,
--   $$\mathbb E\,\mathrm{tr}\,H(E_D)^{2m}\le 4N^2\Big((4QN^3)^m\,m!+\big(8N^2/3\big)^{2m}(2m)!\Big).$$
--
--   This is the moment bound behind the sampler: a list of $Q$ samples estimates the average of a bounded matrix against all selectors at once, with error governed by $\|E_D\|$.
--
--   **Formalization Note.** The expectation is the average of $\mathrm{tr}\,H(E_D)^{2m}$ over all $N^{2Q}$ sample lists `Fin Q → Fin N × Fin N`.
--
--   Differences from the source:
--   - encoding: E over independent uniform pairs → the average over all N^{2Q} lists; reason: the uniform product distribution on a finite set; same value
-- source:
--   Dev Nag, Near-Cubic Gate and Near-Quartic Wire Lower Bounds for SYM∘THR Circuits, STOC 2027 submission, Zenodo doi:10.5281/zenodo.23847026 (sha256 02f54f02…), p. 15, Lemma 4.1

import Mathlib
import Definitions.Def_SymThrWires_Main_Sampling

namespace SymThrWires.Main

/-- **Lemma 4.1** (Trace bound for entries in `[−1, 1]`, p. 15). For every positive integer `m`, if
`D` is a real `N × N` matrix with entries in `[−1, 1]` and the `Q` sample pairs are independent and
uniform on `[N]²`, then `E tr H(E_D)^{2m} ≤ 4N²((4QN³)^m m! + (8N²/3)^{2m} (2m)!)`. The expectation
is the average over all `N^{2Q}` sample lists. -/
theorem lemma_4_1 (N Q m : ℕ) (hm : 1 ≤ m) (D : Matrix (Fin N) (Fin N) ℝ)
    (hD : ∀ u v, |D u v| ≤ 1) :
    (∑ S : Fin Q → Fin N × Fin N, Matrix.trace (dilation (errorMatrix D S) ^ (2 * m))) /
        (Fintype.card (Fin Q → Fin N × Fin N) : ℝ) ≤
      4 * (N : ℝ) ^ 2 * ((4 * (Q : ℝ) * (N : ℝ) ^ 3) ^ m * (m.factorial : ℝ) +
        (8 * (N : ℝ) ^ 2 / 3) ^ (2 * m) * ((2 * m).factorial : ℝ)) := by sorry

end SymThrWires.Main
