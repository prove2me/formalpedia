-- Prove2me | Theorems.Thm_RGGDetect_lemma_3
-- name    : RGGDetect.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:40:00.122238+00:00
-- url     : https://prove2.me/theorems/f2fe19cc-dfc0-4a16-8a73-17d2e1a66627
-- title:
--   Lemma 3 — dropping internal edges
-- statement:
--   Let $D\in\mathcal H_{\boldsymbol\ell}$ be nonzero, $u\in V$, $I=V^c$, and assume $|V|=O(1)$. Then there is a constant $C$, depending only on $|V|$ and $t(D)$, such that
--
--   $$
--   \mathrm{Post}(D)\le C\,g(D)+4\,\mathbb E\big[\mathbb E[D\mid G_{-u},Y_I]^2\big]. \tag{29}
--   $$
--
--   After an error of the order of the target scale $g(D)$, the edges between $u$ and the other vertices of $V$ no longer appear in the conditioning.
--
--   **Formalization Note** In the regime (1): for every bound $B$ on $|V|$ and half-degree $t$, $C>0$ is chosen before the sequences, and (29) holds for all large $n$, every $V$ with $|V|\le B$, positive $\boldsymbol\ell$ with $\|\boldsymbol\ell\|_1=2t$, nonzero $D\in\mathcal H_{\boldsymbol\ell}$ and $u\in V$.
--
--   Differences from the source:
--   - generalization: the standing hypotheses (1) of Theorem 1, for all n → sequences in `Regime δ p d τ`: each hypothesis for all large n; reason: the statement is asymptotic, so sequences satisfying (1) for all n are covered
--   - encoding: |V| = O(1), C depending only on |V| and t(D) → for each bound B on |V| and each t, a constant C chosen before the sequences, valid for all |V| ≤ B; reason: the meaning of O(1) with the paper's convention on constants
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Lemma 3, eq. (29), p.11 (PDF p.13)

import Mathlib
import Definitions.Def_RGGDetect_Regime
import Definitions.Def_RGGDetect_cavity
import Definitions.Def_RGGDetect_harmPoly

open Filter Topology MeasureTheory

namespace RGGDetect

/-- **Lemma 3** (dropping internal edges; arXiv:2610.08517, held version, sha256 e7bebd4a…, Lemma 3,
p.11, eq. (29)): assume `|V| = O(1)`. Then there is a constant `C`, depending only on `|V|` and
`t(D)`, such that `Post(D) ≤ C g(D) + 4 E[(E[D | G_{-u}, Y_I])²]`, `I = V^c`.

**Formalization Note** In the regime (1): for every `δ > 0`, bound `B` on `|V|` and half-degree `t`,
a constant `C` is chosen before the sequences; the inequality holds for all large `n`, for every `V`
with `|V| ≤ B`, positive multidegree `ℓ` with `‖ℓ‖₁ = 2t`, nonzero `D ∈ H_ℓ` and marked `u ∈ V`. The
second term conditions on the pair `(G_{-u}, Y_I)`. -/
theorem lemma_3 (δ : ℝ) (hδ : 0 < δ) (B t : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : ℕ → ℝ) (d : ℕ → ℕ) (τ : ℕ → ℝ), Regime δ p d τ → ∀ᶠ n in atTop,
      ∀ (V : Finset (Fin n)) (ℓ : Fin n → ℕ), V.card ≤ B → (∀ v ∈ V, 1 ≤ ℓ v) →
      ∑ v ∈ V, ℓ v = 2 * t → ∀ D : Config n (d n) → ℝ, D ∈ tensorHarm V ℓ → D ≠ 0 → ∀ u ∈ V,
        Post (τ n) D ≤ C * gD (τ n) V ℓ D +
          4 * postMoment (fun x => (graphMinus (τ n) u x, rowY (τ n) u Vᶜ x)) D := by sorry

end RGGDetect
