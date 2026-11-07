-- Prove2me | Theorems.Thm_StationarityTest_lemma_5_3
-- name    : StationarityTest.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:49.843018+00:00
-- url     : https://prove2.me/theorems/81afe709-6056-4e5f-9344-af8d28101579
-- title:
--   Lemma 5.3 — $\Gamma_H\cup\Lambda$ is a $(2k(d+\Delta),D,c_{gr}(1+2k|\Lambda|))$ Hamiltonian
-- statement:
--   Let $d,D\ge1$, $c_{gr}\ge1$, and let $\Gamma\subseteq S^k_{[n]}$ be the clause set of a $(d,D,c_{gr})$ Hamiltonian $H$. Let $\Lambda\subseteq S^k_{[n]}$ be a set of clauses whose interaction graph has degree at most $\Delta$, self-edges included. Then the union $\Gamma_{H,\Lambda}:=\Gamma\cup\Lambda$ is the clause set of a $(\hat d,D,\hat c_{gr})$ Hamiltonian with
--
--   $$\hat d=2k(d+\Delta),\qquad \hat c_{gr}=c_{gr}\,(1+2k|\Lambda|).$$
--
--   The degree $\hat d$ does not depend on $|\Lambda|$, while the growth constant does. This is what lets the structure learning algorithm add a neighbourhood $\Lambda$ of radius $\ell$ to the current guess and still apply the locality estimates proved for lattice Hamiltonians.
--
--   Differences from the source:
--   - encoding: "(d̂, D, ĉ_gr) Hamiltonian, where d̂ ≤ 2k(d + ∆), ĉ_gr ≤ c_gr(1 + 2k|Λ|)" → IsDDcgr (2k(d + Δ)) D (c_gr(1 + 2k|Λ|)) (Γ ∪ Λ); reason: Definition 2.2 is monotone in d and c_gr, so the two forms say the same
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Lemma 5.3, (104), p.29 (proof (105)–(106), p.30)

import Definitions.Def_StationarityTest_Geometry

namespace StationarityTest

/-- **Lemma 5.3**, p.29 (Bergamaschi, *The stationarity test*, arXiv:2610.01074, held file
sha256 0b7e46fb…). Let `H` be a `(d, D, c_gr)` Hamiltonian with clause set `Γ`, and `Λ ⊆ S^k_[n]`
a set of clauses whose interaction graph has degree `≤ Δ`. Then `Γ_{H,Λ} := Γ ∪ Λ` is a
`(d̂, D, ĉ_gr)` Hamiltonian with `d̂ ≤ 2k(d + Δ)` and `ĉ_gr ≤ c_gr(1 + 2k|Λ|)` (104).

**Formalization Note.** The conclusion is stated with `d̂ = 2k(d + Δ)` and
`ĉ_gr = c_gr(1 + 2k|Λ|)`, which is the same claim (Definition 2.2 is monotone in `d` and `c_gr`).
Degrees count self-edges (Definition 2.2); `d, D ≥ 1`, `c_gr ≥ 1` are the ranges of
Definition 2.2. -/
theorem lemma_5_3 {n q k d D Δ : ℕ} {cgr : ℝ} (hd : 1 ≤ d) (hD : 1 ≤ D) (hcgr : 1 ≤ cgr)
    (Γ Λ : Finset (KLocal n q k)) (hΓ : IsDDcgr d D cgr Γ) (hΛ : DegreeLe Λ Δ) :
    IsDDcgr (2 * k * (d + Δ)) D (cgr * (1 + 2 * k * (Λ.card : ℝ))) (Γ ∪ Λ) := by sorry

end StationarityTest
