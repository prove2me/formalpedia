-- Prove2me | Theorems.Thm_StationarityTest_lemma_A_4
-- name    : StationarityTest.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:17.461192+00:00
-- url     : https://prove2.me/theorems/e9bf2a54-52a2-4c9e-a179-e4b499d5a96f
-- title:
--   Lemma A.4 — $\|\mathcal L^\dagger_{H,a}-\mathcal L^\dagger_{G,a}\|_{\infty-\infty}\le32\beta d\sum_\gamma|g_\gamma-h_\gamma|e^{-\theta\,\mathrm{dist}(i,\gamma)}$
-- statement:
--   Let $\Gamma\subseteq S^k_{[n]}$ be a clause set whose interaction graph has degree at most $d$ (self-edges included). Let $H=\sum_{\gamma\in\Gamma}h_\gamma P_\gamma$ and $G=\sum_{\gamma\in\Gamma}g_\gamma P_\gamma$ with $|h_\gamma|,|g_\gamma|\le1$, and let $\beta>0$. Fix a site $i$ and a single-site Pauli operator $A^a$ on $i$, and take $\sigma=\beta^{-1}$. Then
--
--   $$\big\|\mathcal L^\dagger_{H,a}-\mathcal L^\dagger_{G,a}\big\|_{\infty-\infty}\le32\beta d\sum_{\gamma\in\Gamma}|g_\gamma-h_\gamma|\,e^{-\theta\cdot\operatorname{dist}(i,\gamma)},\qquad\theta=\min\{1,(8e\beta d)^{-1}\}.$$
--
--   A clause at infinite distance from $i$ contributes $0$. This is the master continuity estimate of the paper: the Heisenberg-picture generator of a single-site jump depends on the Hamiltonian coefficients in a Lipschitz way, with weights decaying exponentially in the distance from the jump. Corollaries A.5 and A.6 are its two special cases.
--
--   Differences from the source: none.
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Lemma A.4, (246), p.58 (proof (247)–(257), pp.58–59)

import Definitions.Def_StationarityTest_Geometry
import Definitions.Def_StationarityTest_Lindbladian

namespace StationarityTest

/-- **Lemma A.4 (Lipschitz Continuity of L)**, p.58 (Bergamaschi, *The stationarity test*,
arXiv:2610.01074, held file sha256 0b7e46fb…). Let `H = Σ_{γ∈Γ} h_γ P_γ`, `G = Σ_{γ∈Γ} g_γ P_γ`
be Hamiltonians on the same degree `≤ d` interaction graph, fix a site `i`, a single-site Pauli
operator `A_a` on `i` and `σ = β^{−1}`. Then
`∥L†_{H,a} − L†_{G,a}∥_{∞−∞} ≤ 32βd Σ_{γ∈Γ} |g_γ − h_γ| e^{−θ·dist(i,γ)}` with
`θ := min{1, (8eβd)^{−1}}` (246).

**Formalization Note.** `|h_γ|, |g_γ| ≤ 1` is the standing assumption (21) (it is used through
Lemma A.1). `e^{−θ·dist(i,γ)} = 0` when no clause of `Γ` containing `i` is connected to `γ`. -/
theorem lemma_A_4 {n q k d : ℕ} (Γ : Finset (KLocal n q k)) (hdeg : DegreeLe Γ d)
    (h g : KLocal n q k → ℝ) (hh : ∀ γ ∈ Γ, |h γ| ≤ 1) (hg : ∀ γ ∈ Γ, |g γ| ≤ 1)
    {β : ℝ} (hβ : 0 < β) (i : Fin n) (a : PauliString n q) (ha : a ∈ singleSite i) :
    superNorm (fun O => adjointSO (lindblad (ham Γ h) β a.mat) O -
        adjointSO (lindblad (ham Γ g) β a.mat) O) ≤
      32 * β * d * ∑ γ ∈ Γ, |g γ - h γ| *
        expDecay (min 1 (8 * Real.exp 1 * β * d)⁻¹) (siteDist Γ i γ) := by sorry

end StationarityTest
