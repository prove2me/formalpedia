-- Prove2me | Theorems.Thm_PersistQMem_lemma_6_4
-- name    : PersistQMem.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:48:39.41482+00:00
-- url     : https://prove2.me/theorems/44133c49-6a4a-45e6-bc94-1f2c749ebe63
-- title:
--   Lemma 6.4 — exact inverse loss: $d_{j,z}(uu^*,H)/\alpha\le z\theta\ell_j(X)-(1-\theta)mJ(X)$, $J(X)=\langle X,\Delta X\rangle_\sigma$, $d_{j,z}(uu^*,H)\le c_{\alpha,\theta}b_j$
-- statement:
--   Fix the data of Definition 2.1, $0<\theta<1$, $\alpha>1$, a label $(j,z)$ with $z\in\{-1,1\}$, a complete refined instrument with entering memory $\mathbb C^r$, a unit vector $u\in\mathbb C^r$ and a recorded Hermitian contraction $H=\bigoplus_aH_a$. Define (48)
--   $$T=I-H/\alpha,\quad X=T^{-1},\quad v=Vu,\quad m=1-1/\alpha,\quad J(X)=\|(I-VV^*)\hat Xv\|^2 .$$
--   Then
--   $$\frac{d_{j,z}(uu^*,H)}\alpha\le z\theta\ell_j(X)-(1-\theta)mJ(X),\qquad J(X)=\langle X,\Delta X\rangle_\sigma,\tag{49}$$
--   and, completing the square,
--   $$d_{j,z}(uu^*,H)\le c_{\alpha,\theta}b_j,\qquad c_{\alpha,\theta}=\frac{\alpha^2\theta^2}{4(1-\theta)(\alpha-1)}.\tag{50}$$
--
--   The identity $J(X)=\langle X,\Delta X\rangle_\sigma$ is what lets the quadratic loss pay for the linear response.
--
--   Differences from the source:
--   - encoding: J(X) = ⟨X, ΔX⟩_σ → X is a Hermitian recorded test (asserted) and J(X) equals the H_σ inner product of its class with Δ of it; reason: ⟨·,Δ·⟩_σ is defined on Hermitian tests; the statement also asserts that X is one
--   - encoding: H_σ, the quotient of Hermitian recorded tests by zero-variance tests → the range of the isometric real-linear map π X = ⊕_a (X_a − Tr(σX) I) L_a in real coordinates (Hsig); maps on tests are transported through a fixed linear section; reason: π is isometric for ⟨·,·⟩_σ and its kernel is the zero-variance tests, so its range is the quotient; maps that vanish on zero-variance tests do not depend on the section
--   - encoding: z ∈ {−1, 1} → z : Bool with zsign true = 1, zsign false = −1; reason: Lean convention; same two signs
--   - encoding: real traces Tr(·) (drift, ℓ_j, Tr A) → real parts of complex traces; reason: the traces are real for the Hermitian and positive operators involved
--   - encoding: unit vector u ∈ C^r → u : Fin r → ℂ with star u ⬝ᵥ u = 1; reason: Lean convention; same vectors
--   - reading: “any recorded contraction H” → H a recorded Hermitian contraction (every block Hermitian with −I ⪯ H_a ⪯ I); reason: the drift d_{j,z}(A, H) of (44), p.23, is defined for recorded Hermitian contractions, and the proof's spectral intervals (51) use that H is Hermitian
--   - generalization: entering memory C^r with r ≤ K (§6.2 standing assumption, p.19) → no relation between r and K is assumed; reason: the statement involves K only through the instrument's output bound k_a ≤ K, which also holds with K replaced by max(r, K), so every instance is an instance of the source's lemma at that memory bound; r ≤ K is the source's case
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), Lemma 6.4, (48)–(50), p.24 (PDF p.27)

import Mathlib
import Definitions.Def_PersistQMem_Hsig
import Definitions.Def_PersistQMem_drift

open scoped Matrix ComplexOrder InnerProductSpace

namespace PersistQMem

/-- **Lemma 6.4 (Exact inverse loss), p.24** (Tao, Shen, *Structural Lower Bounds for Quantum
Property Estimation with Persistent Memory*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 6d48ad24…, Lemma 6.4, p.24). Fix the data of Definition 2.1, `0 < θ < 1`, `α > 1`, a label
`(j, z)`, a complete refined instrument `Φ`, a unit entering vector `u ∈ C^r` and a recorded
Hermitian contraction `H = ⊕_a H_a`. With `T = I − H/α`, `X = T⁻¹`, `v = Vu`, `m = 1 − 1/α` and
`J(X) = ‖(I − VV*) X̂ v‖²` (48):
1. (49) `d_{j,z}(uu*, H)/α ≤ zθ ℓ_j(X) − (1 − θ) m J(X)`;
2. (49) `X` is a Hermitian test and `J(X) = ⟨X, ΔX⟩_σ`;
3. (50) `d_{j,z}(uu*, H) ≤ c_{α,θ} b_j` with `c_{α,θ} = α²θ²/(4(1 − θ)(α − 1))`.

**Formalization Note.** `ℓ_j(X) = Tr(δ_j X)` is written as the real part of the trace pairing (the
trace is real). `z ∈ {−1, 1}` is a Boolean through `zsign`. -/
theorem lemma_6_4 {D M : ℕ} {G : Fin M → Matrix (Fin D) (Fin D) ℂ} {p : Fin M → ℝ}
    (hG : ProfileData G p) {ι : Type} [Fintype ι] [DecidableEq ι] {r K : ℕ}
    (Φ : FinInstrument ι r D K) (u : Fin r → ℂ) (hu : star u ⬝ᵥ u = 1)
    (α : ℝ) (hα : 1 < α) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (j : Fin M) (z : Bool)
    (H : RecTest Φ) (hH : IsRecHermContraction Φ H) :
    drift Φ α (rhoAlt θ (G j) z) (uuStar u) H / α ≤
      zsign z * θ * (recTrace Φ (deltaOut Φ u (G j)) (invTest Φ α H)).re -
        (1 - θ) * (1 - 1 / α) * invLossJ Φ u (invTest Φ α H) ∧
    (∃ hX : invTest Φ α H ∈ hermTests Φ, invLossJ Φ u (invTest Φ α H) =
      ⟪toHsig Φ u ⟨invTest Φ α H, hX⟩, Delta Φ u (toHsig Φ u ⟨invTest Φ α H, hX⟩)⟫_ℝ) ∧
    drift Φ α (rhoAlt θ (G j) z) (uuStar u) H ≤
      α ^ 2 * θ ^ 2 / (4 * (1 - θ) * (α - 1)) * bcoef Φ u (G j) := by sorry

end PersistQMem
