-- Prove2me | Theorems.Thm_QuadSDE_lemma_1
-- name    : QuadSDE.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:15:24.557573+00:00
-- url     : https://prove2.me/theorems/68993168-db5b-4a28-ad75-a388ed0fb835
-- title:
--   Lemma 1 — $c_{ijk}+c_{jki}+c_{kij}=0$, $\sum_jc_{jji}=\sum_jc_{ijj}=0$, columns have at most $2s$ nonzeros
-- statement:
--   Let $c_{ijk}$ be the coefficients of an admissible quadratic drift on $\mathbb R^N$: symmetric, $c_{ijk}=c_{ikj}$, norm preserving (6) and volume preserving (7). Then:
--   1. for all indices $i,j,k\in[N]$,
--   $$c_{ijk}+c_{jki}+c_{kij}=0\qquad(14);$$
--   2. for every index $i\in[N]$,
--   $$\sum_{j=1}^Nc_{jji}=0\qquad\text{and}\qquad\sum_{j=1}^Nc_{ijj}=0\qquad(15);$$
--   3. if the drift is $s$-sparse (every row of the $N\times N^2$ matrix $c$ has at most $s$ nonzeros), then every column of $c$ has at most $2s$ nonzeros.
--
--   This is the coefficient form of norm and volume preservation used throughout the analysis of the Kolmogorian, and the bound $r\le2s$ linking the succinct and the oracle models.
--
--   Differences from the source:
--   - reading: Thus we can assume wlog r ≤ 2s → not a separate clause; the column bound it rests on is clause 4 (channelsLE c (2 s)); reason: the sentence is a remark drawn from the column bound
--   - encoding: ∂f_i/∂x_i in (7); indices in [N] → Fréchet derivative of x ↦ f_i(x) in direction e_i; Fin N; reason: Lean convention; same instances
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §3, Lemma 1, p. 13

import Mathlib
import Definitions.Def_QuadSDE_DriftClass

namespace QuadSDE

/-- **Lemma 1 (coefficient form of norm and volume preservation; column bound).**
Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), §3, Lemma 1, p. 13: "For
any indices `i, j, k ∈ [N]` one has `c_ijk + c_jki + c_kij = 0`. (14) For any index `i ∈ [N]` one
has `Σ_{j=1}^N c_jji = 0` and `Σ_{j=1}^N c_ijj = 0`. (15) Furthermore, any column of `c` contains
at most `2s` nonzeros. Thus we can assume wlog `r ≤ 2s`."

For an admissible quadratic drift (symmetric coefficients, Eqs. (5)–(7)):
1. `c_{ijk} + c_{jki} + c_{kij} = 0` for all `i, j, k`;
2. `Σ_j c_{jji} = 0` for all `i`;
3. `Σ_j c_{ijj} = 0` for all `i`;
4. if the drift is `s`-sparse, every column of `c` has at most `2s` nonzeros.

**Formalization Note.** "Thus we can assume wlog `r ≤ 2s`" is a remark: clause 4 is the column
bound it rests on. -/
theorem lemma_1 {N : ℕ} (c : Coeff N) (hc : IsAdmissibleDrift c) :
    (∀ i j k, c i j k + c j k i + c k i j = 0) ∧
    (∀ i, ∑ j, c j j i = 0) ∧
    (∀ i, ∑ j, c i j j = 0) ∧
    ∀ s : ℕ, sparsityLE c s → channelsLE c (2 * s) := by sorry

end QuadSDE
