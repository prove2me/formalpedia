-- Prove2me | Theorems.Thm_PlatonicJEPA_k_pairs_identify_rotation
-- name    : PlatonicJEPA.k_pairs_identify_rotation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T12:23:02.935044+00:00
-- url     : https://prove2.me/theorems/489230ad-b8b9-4482-a781-03bb063a6f93
-- title:
--   Proposition 2: $k$ pairs identify the rotation
-- statement:
--   (i) Every rotation of a whitened embedding is whitened, so no statistic of the first two moments of unpaired samples identifies the rotation between two modalities.
--
--   (ii) Suppose $h_1=Qh_2$ for some $Q\in O(k)$, as for two minimisers in the setting of Theorem 1 and Proposition 1. If the embeddings $h_2(z_1),\dots,h_2(z_n)$ of $n\ge k$ world states span $\mathbb{R}^k$, then $Q$ is the unique minimiser over $R\in O(k)$ of
--
--   $$\sum_{i\le n}\|h_1(z_i)-Rh_2(z_i)\|^2$$
--
--   (orthogonal Procrustes).
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), Section 2.2, Proposition 2, p. 4

import Mathlib
import Definitions.Def_PlatonicJEPA_Basic

open MeasureTheory Filter Topology

namespace PlatonicJEPA

theorem k_pairs_identify_rotation {Z : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ}
    (p : Z → ℝ) (h₁ h₂ : Z → Fin k → ℝ) :
    (∀ Q : Matrix.orthogonalGroup (Fin k) ℝ,
      IsWhitened p h₁ → IsWhitened p (fun z => rot Q (h₁ z))) ∧
    (∀ (Q : Matrix.orthogonalGroup (Fin k) ℝ), (∀ z, h₁ z = rot Q (h₂ z)) →
      ∀ (n : ℕ) (zs : Fin n → Z), k ≤ n →
        Submodule.span ℝ (Set.range fun i => h₂ (zs i)) = ⊤ →
        ∀ R : Matrix.orthogonalGroup (Fin k) ℝ,
          ((∀ R' : Matrix.orthogonalGroup (Fin k) ℝ,
              ∑ i, sqNorm (h₁ (zs i) - rot R (h₂ (zs i))) ≤
                ∑ i, sqNorm (h₁ (zs i) - rot R' (h₂ (zs i)))) ↔ R = Q)) := by sorry

end PlatonicJEPA
