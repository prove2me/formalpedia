-- Prove2me | Theorems.Thm_QTDecode_Parallel_lemma_17
-- name    : QTDecode.Parallel.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:00.533837+00:00
-- url     : https://prove2.me/theorems/692b5923-11d5-4017-afde-291ee88a0045
-- title:
--   Lemma 17, p. 24 — the preprocessing mismatch satisfies |Z| ≤ 4|e| and ‖Z‖ ≤ 4|e|/(κΔ)
-- statement:
--   Let $|A|=|B|=\Delta$, let the dual tensor code $C_A\otimes\mathbb F_2^B+\mathbb F_2^A\otimes C_B$ be $\kappa$-product-expanding ($\kappa>0$), and let $e\in\mathbb F_2^Q$ be a $\sigma_x$-type error. In the preprocessing phase (Algorithm 1, lines 2–4) every vertex $v\in V_1=V_{01}\cup V_{10}$ picks a minimum-weight local error $\varepsilon_v$ on $Q(v)$ whose local syndrome coincides with that of $e$, i.e. $e_v+\varepsilon_v$ is a dual tensor codeword, and the mismatch is $Z=\sum_{v\in V_1}\varepsilon_v$. Then
--   $$|Z|\le 4|e|\qquad\text{and}\qquad \|Z\|\le\frac{4}{\kappa\Delta}\,|e|,$$
--   where $\|Z\|$ is the least norm $\|C_0\|+\|R_0\|+\|C_1\|+\|R_1\|$ of a decomposition $Z=C_0+R_0+C_1+R_1$ (eqs. (4)–(5)).
--
--   Both bounds are the starting point for tracking the mismatch during decoding (Lemma 19, Theorem 20).
--
--   **Formalization Note** $\|Z\|\le\ldots$ is stated as the existence of a decomposition with norm at most $\frac{4}{\kappa\Delta}|e|$. The local corrections $\varepsilon_v$ may be any minimizers.
-- source:
--   Leverrier and Zémor, Decoding quantum Tanner codes, arXiv:2208.05537v3, p. 24, Lemma 17, eq. (6)

import Mathlib
import Definitions.Def_QTDecode_Parallel_Model

namespace QTDecode.Parallel

open QAlgorithms

/-- Lemma 17, p. 24. Let the dual tensor code `C_A ⊗ F₂^B + F₂^A ⊗ C_B` be `κ`-product-expanding
(`|A| = |B| = Δ`, `κ > 0`), `e` a `σ_x`-type error, and `Z = Σ_{v ∈ V₁} ε_v` the mismatch of the
preprocessing phase, `ε_v` any minimum-weight local error with the local syndrome of `e` at
`v ∈ V₁`. Then `|Z| ≤ 4|e|` (eq. (6)) and `‖Z‖ ≤ (4/(κΔ))|e|`: some decomposition (4) of `Z` has
norm (5) at most `(4/(κΔ))|e|`. -/
theorem lemma_17 {G : Type} [Group G] [Fintype G] [DecidableEq G] (A B : Finset G) (Δ : ℕ) (κ : ℝ)
    (hA : A.card = Δ) (hB : B.card = Δ) (hκ : 0 < κ)
    (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (hexp : IsProductExpanding CA CB Δ κ)
    (e : G × A × B → ZMod 2) (εsel : G × (Bool × Bool) → A × B → ZMod 2)
    (hεsel : ∀ v : G × (Bool × Bool), v.2.1 ≠ v.2.2 → IsMinLocalCorrection CA CB e v (εsel v)) :
    (hammingNorm (qtMismatch εsel) : ℝ) ≤ 4 * (hammingNorm e : ℝ) ∧
    ∃ D : Decomp (G × A × B), IsDecomp CA CB (qtMismatch εsel) D ∧
      (decompNorm D : ℝ) ≤ 4 / (κ * Δ) * (hammingNorm e : ℝ) := by sorry

end QTDecode.Parallel
