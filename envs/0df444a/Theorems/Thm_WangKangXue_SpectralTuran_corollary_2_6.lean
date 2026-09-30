-- Prove2me | Theorems.Thm_WangKangXue_SpectralTuran_corollary_2_6
-- name    : WangKangXue.SpectralTuran.corollary_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:24:55.369925+00:00
-- url     : https://prove2.me/theorems/0112be83-4d19-401c-94f7-35aeda524402
-- title:
--   Corollary 2.6 — spectral stability for graphs of chromatic number r + 1
-- statement:
--   Let $r \ge 2$ and let $F$ be a graph with chromatic number $\chi(F) = r+1$. For every $\varepsilon > 0$ there exist $\delta > 0$ and $n_0$ such that the following holds: if $G$ is an $F$-free graph on $n \ge n_0$ vertices with
--   $$
--   \lambda(G) \ \ge\ \Big(1 - \frac1r - \delta\Big) n,
--   $$
--   then $G$ can be obtained from $T_{n,r}$ by adding and deleting at most $\varepsilon n^2$ edges in total. That is, for some labelling of $T_{n,r}$ on the vertex set of $G$,
--   $$
--   |E(G) \setminus E(T_{n,r})| + |E(T_{n,r}) \setminus E(G)| \le \varepsilon n^2 .
--   $$
--
--   This is the spectral analogue of the Erdős–Simonovits stability theorem, derived in the paper from Nikiforov's spectral stability lemma (Lemma 2.5); it is the entry point of the structural analysis in Lemma 3.3.
--
--   **Formalization Note** "A labelling of $T_{n,r}$" is a graph $H$ on the vertex set of $G$ isomorphic to Mathlib's `turanGraph n r`. The corollary's text does not restate $r \ge 2$; it is taken from the surrounding context (Lemma 2.5 and Theorem 1.2 both assume it).
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, p. 3, Corollary 2.6

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad

namespace WangKangXue.SpectralTuran

open Classical

/-- **Corollary 2.6** (Wang–Kang–Xue, arXiv:2203.10831v1, p. 3). Let `F` be a graph with
chromatic number `χ(F) = r + 1` (`r ≥ 2`). For every `ε > 0` there exist `δ > 0` and `n₀` such
that every `F`-free graph `G` on `n ≥ n₀` vertices with `λ(G) ≥ (1 − 1/r − δ) n` can be obtained
from (a relabelled copy `H` of) `T_{n,r}` by adding and deleting at most `ε n²` edges in total. -/
theorem corollary_2_6 {W : Type*} [Fintype W] (F : SimpleGraph W) (r : ℕ) (hr : 2 ≤ r)
    (hχ : F.chromaticNumber = ((r + 1 : ℕ) : ℕ∞)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n),
      F.Free G → (1 - 1 / (r : ℝ) - δ) * n ≤ specRad G →
      ∃ H : SimpleGraph (Fin n), Nonempty (H ≃g SimpleGraph.turanGraph n r) ∧
        ((G.edgeFinset \ H.edgeFinset).card + (H.edgeFinset \ G.edgeFinset).card : ℝ) ≤
          ε * (n : ℝ) ^ 2 := by sorry

end WangKangXue.SpectralTuran
