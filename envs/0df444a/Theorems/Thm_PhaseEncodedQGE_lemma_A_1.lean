-- Prove2me | Theorems.Thm_PhaseEncodedQGE_lemma_A_1
-- name    : PhaseEncodedQGE.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:50:27.899685+00:00
-- url     : https://prove2.me/theorems/92c1568a-7293-49fe-9586-e9556187ca7f
-- title:
--   Lemma A.1 — generator form $p_1(x)=\operatorname{Im}[\overline{\phi(x)}\sum_{b=1}^r(E^{r-b}\Sigma E^b\phi_{\mathrm{prep}})(x)]$
-- statement:
--   Let $G$ be a cubic graph, $\phi_{\mathrm{prep}}$ any preparation vector, $\sigma\in\{X,Y\}$ the mixer generator and $r\ge1$. Write $p(x;\beta)=|\psi(x;\beta)|^2$ with $\psi(\beta)=(U(\beta)E)^r\phi_{\mathrm{prep}}$, where $E$ is the edge-phase diagonal and $U(\beta)=\bigotimes_je^{-i\beta\sigma_j/2}$; let $\phi=E^r\phi_{\mathrm{prep}}$ be the pre-mixer amplitude and $p_1=\partial_\beta p|_{\beta=0}$. With $\Sigma=\sum_j\sigma_j$,
--   $$p_1(x)=\operatorname{Im}\Bigl[\overline{\phi(x)}\sum_{b=1}^{r}\bigl(E^{r-b}\,\Sigma\,E^{b}\phi_{\mathrm{prep}}\bigr)(x)\Bigr].$$
--
--   This reduces the first-order Born term to single-qubit generator actions on the pre-mixer amplitude.
--
--   Differences from the source:
--   - generalization: $\phi_{\mathrm{prep}}$ the preparation of the circuit (degree-aware $R_X$ or Hadamard) → an arbitrary vector of amplitudes; reason: the proof (product rule at β = 0) uses no property of φ_prep, so the paper's preparations are special cases
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), App. A.1.1, p.13 (PDF p.14), Lemma A.1, eq. (20)

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Circuit
set_option autoImplicit false

namespace PhaseEncodedQGE

open Matrix

/-- Lemma A.1, the generator form of the first-order term (Miller, Lee, *Structural Accessibility in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), App. A.1.1, p.13, eq. (20)).

Let `p(x; β) = |ψ(x; β)|²` with `ψ(β) = (U(β)E)^r ϕ_prep`, where `E` is the edge-phase diagonal,
`U(β) = ⨂_j e^{−iβσ_j/2}` with `σ ∈ {X, Y}` the mixer generator and `r ≥ 1`; let `ϕ = E^r ϕ_prep`
and `p₁ = ∂_β p|_{β=0}`. With `Σ = ∑_j σ_j`,
`p₁(x) = Im[ \overline{ϕ(x)} ∑_{b=1}^{r} (E^{r−b} Σ E^b ϕ_prep)(x) ]`.

**Formalization Note** `ϕ_prep` is an arbitrary vector of amplitudes. The conjugate is
`starRingEnd ℂ`; `r − b` is natural-number subtraction with `b ≤ r`. -/
theorem lemma_A_1 (n : ℕ) (G : SimpleGraph (Fin n)) (hG : IsCubic G) (prep : Outcome n → ℂ)
    (P : Axis) (r : ℕ) (hr : 1 ≤ r) (γ : ℝ) (x : Outcome n) :
    bornDeriv prep P r G γ x =
      (starRingEnd ℂ (preMixer prep r G γ x) *
        ∑ b ∈ Finset.Icc 1 r,
          ((edgeMat G γ ^ (r - b) * generator P * edgeMat G γ ^ b) *ᵥ prep) x).im := by sorry

end PhaseEncodedQGE
