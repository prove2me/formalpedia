-- Prove2me | Theorems.Thm_StationarityTest_lemma_3_6
-- name    : StationarityTest.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:27.737486+00:00
-- url     : https://prove2.me/theorems/86e9a2ad-517c-4b44-9557-b4c4cf727aa0
-- title:
--   Lemma 3.6 ([CAN25, Lemma III.6]) — $\|B\|_{\tau_R}\le c^{|R|\beta d\log2\beta d}\|B\|_{\rho_G}$
-- statement:
--   There is a universal constant $c>0$ with the following property. Let $G=\sum_{\gamma\in\Gamma}g_\gamma P_\gamma$ be a Hamiltonian with $|g_\gamma|\le1$ whose interaction graph has degree at most $d$. Let $\beta d\ge1$, and let $B$ be an operator supported on a region $R\subseteq[n]$. Then
--
--   $$\|B\|_{\tau_R}\le c^{\,|R|\cdot\beta d\log(2\beta d)}\cdot\|B\|_{\rho_G}.$$
--
--   Here $\|\cdot\|_{\rho_G}$ is the KMS norm of the Gibbs state and $\|\cdot\|_{\tau_R}$ the normalized Hilbert–Schmidt norm. The Gibbs KMS norm of a local operator is therefore comparable to its unweighted norm, at a cost exponential in the size of its support. This converts commutator bounds in the KMS norm into bounds on individual Pauli coefficients (60).
--
--   **Formalization Note** $c$ is chosen before every other parameter, including $n,q,k,d$.
--
--   Differences from the source:
--   - reading: "∥B∥_{τ_R}" (τ_R is not defined in the paper) → the KMS norm of the maximally mixed state I/2^{nq}; reason: for B supported on R this is the normalized Hilbert–Schmidt norm on R, the only sense in which (60) holds with the factor 2^{2q+1}
--   - reading: "a local operator with support on a region R" → a linear combination of Pauli strings whose site supports lie in R; reason: Pauli strings span all operators, so this is B = B_R ⊗ I
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Lemma 3.6, (59), p.21

import Definitions.Def_StationarityTest_Geometry
import Definitions.Def_StationarityTest_Fisher

namespace StationarityTest

/-- **Lemma 3.6** ([CAN25, Lemma III.6]), p.21 (Bergamaschi, *The stationarity test*,
arXiv:2610.01074, held file sha256 0b7e46fb…). Let `B` be a local operator supported on a region
`R`. For any Hamiltonian `G` of bounded degree `d` and `β ≥ d^{−1}`,
`∥B∥_{τ_R} ≤ c^{|R|·βd log 2βd} · ∥B∥_{ρ_G}` (59), where `c` is a universal constant.

**Formalization Note.** `c` is universal: `∃ c > 0` before every other parameter (`n, q, k, d`
included). `∥·∥_{ρ_G}` is the KMS norm (27); `∥·∥_{τ_R}` is read as the KMS norm of the maximally
mixed state (the normalized Hilbert–Schmidt norm, see `tauNorm`). `G = Σ_{γ∈Γ} g_γ P_γ` with
`|g_γ| ≤ 1` (21) on a clause set of degree `≤ d` (self-edges counted). `log` is natural; the base
only rescales `c`. -/
theorem lemma_3_6 : ∃ c : ℝ, 0 < c ∧ ∀ {n q k d : ℕ} (Γ : Finset (KLocal n q k)),
    DegreeLe Γ d → ∀ (g : KLocal n q k → ℝ), (∀ γ ∈ Γ, |g γ| ≤ 1) →
    ∀ {β : ℝ}, 1 ≤ β * d → ∀ (R : Finset (Fin n)) (B : Op n q), SupportedOn B R →
    tauNorm B ≤ c ^ ((R.card : ℝ) * (β * d) * Real.log (2 * β * d)) *
      kmsNorm (gibbs β (ham Γ g)) B := by sorry

end StationarityTest
