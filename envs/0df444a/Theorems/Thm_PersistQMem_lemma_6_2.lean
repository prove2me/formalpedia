-- Prove2me | Theorems.Thm_PersistQMem_lemma_6_2
-- name    : PersistQMem.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:47:33.861258+00:00
-- url     : https://prove2.me/theorems/2276d3ba-e138-480e-a036-803e6640c640
-- title:
--   Lemma 6.2 — removing the native directions: $c_j\in\operatorname{ran}\Delta$, $|\ell_j(X)|^2\le b_j\langle X,\Delta X\rangle_\sigma$, $\sum_jp_jb_j\le\sum_jp_j\|c_j\|_\sigma^2+(2r-2)\beta$
-- statement:
--   In the setting of Lemma 6.1 (data of Definition 2.1, a complete refined instrument with entering memory $\mathbb C^r$, a unit vector $u$), every Riesz vector $c_j$ lies in the range of $\Delta$. With
--   $$b_j=\langle c_j,\Delta^+c_j\rangle_\sigma,\tag{33}$$
--   where $\Delta^+$ is the Moore–Penrose pseudoinverse of $\Delta$, every Hermitian recorded test $X$ satisfies
--   $$|\ell_j(X)|^2\le b_j\langle X,\Delta X\rangle_\sigma,\tag{34}$$
--   and
--   $$\sum_jp_jb_j\le\sum_jp_j\|c_j\|_\sigma^2+(2r-2)\beta.\tag{35}$$
--
--   The bound (35) does not depend on the condition number of $\Delta$: memory directions that are preserved almost perfectly carry no source response.
--
--   Differences from the source:
--   - encoding: H_σ, the quotient of Hermitian recorded tests by zero-variance tests → the range of the isometric real-linear map π X = ⊕_a (X_a − Tr(σX) I) L_a in real coordinates (Hsig); maps on tests are transported through a fixed linear section; reason: π is isometric for ⟨·,·⟩_σ and its kernel is the zero-variance tests, so its range is the quotient; maps that vanish on zero-variance tests do not depend on the section
--   - encoding: Δ⁺, the Moore–Penrose pseudoinverse; ⟨X, ΔX⟩_σ → the published HarmonicGames.Decomposition.pinv of Δ on H_σ; the inner product in H_σ of the class of X with Δ applied to it; reason: same operator; Lean convention
--   - encoding: 2r − 2 → 2r − 2 computed in ℝ; reason: no natural-number truncation
--   - encoding: unit vector u ∈ C^r → u : Fin r → ℂ with star u ⬝ᵥ u = 1; reason: Lean convention; same vectors
--   - generalization: entering memory C^r with r ≤ K (§6.2 standing assumption, p.19) → no relation between r and K is assumed; reason: the statement involves K only through the instrument's output bound k_a ≤ K, which also holds with K replaced by max(r, K), so every instance is an instance of the source's lemma at that memory bound; r ≤ K is the source's case
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), Lemma 6.2, (33)–(35), p.21 (PDF p.24)

import Mathlib
import Definitions.Def_PersistQMem_Hsig

open scoped Matrix ComplexOrder InnerProductSpace

namespace PersistQMem

/-- **Lemma 6.2 (Removing the native directions), p.21** (Tao, Shen, *Structural Lower Bounds for
Quantum Property Estimation with Persistent Memory*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 6d48ad24…, Lemma 6.2, p.21). With `C`, `Δ` as in Lemma 6.1: every Riesz vector `c_j` lies in
the range of `Δ`; with `b_j = ⟨c_j, Δ⁺ c_j⟩_σ` (33), `Δ⁺` the Moore–Penrose pseudoinverse of `Δ`,
every Hermitian test `X` satisfies (34) `|ℓ_j(X)|² ≤ b_j ⟨X, ΔX⟩_σ`, and
(35) `Σ_j p_j b_j ≤ Σ_j p_j ‖c_j‖²_σ + (2r − 2)β`.

**Formalization Note.** `⟨X, ΔX⟩_σ` is the inner product in `H_σ` of the class of `X` with `Δ`
applied to it. `2r − 2` is computed in `ℝ`. -/
theorem lemma_6_2 {D M : ℕ} {G : Fin M → Matrix (Fin D) (Fin D) ℂ} {p : Fin M → ℝ}
    (hG : ProfileData G p) {ι : Type} [Fintype ι] {r K : ℕ} (Φ : FinInstrument ι r D K)
    (u : Fin r → ℂ) (hu : star u ⬝ᵥ u = 1) :
    (∀ j, cvec Φ u (G j) ∈ LinearMap.range (Delta Φ u)) ∧
    (∀ j, ∀ X : hermTests Φ, (ellV Φ u (G j) X) ^ 2 ≤
      bcoef Φ u (G j) * ⟪toHsig Φ u X, Delta Φ u (toHsig Φ u X)⟫_ℝ) ∧
    ∑ j, p j * bcoef Φ u (G j) ≤
      ∑ j, p j * ‖cvec Φ u (G j)‖ ^ 2 + (2 * (r : ℝ) - 2) * gramNorm G p := by sorry

end PersistQMem
