-- Prove2me | Theorems.Thm_QDSGibbs_proposition_3_4
-- name    : QDSGibbs.proposition_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:37:37.477215+00:00
-- url     : https://prove2.me/theorems/3909c55d-5da3-4bde-b8eb-3f1ca44e438a
-- title:
--   Proposition 3.4 — Gibbs preservation and KMS detailed balance
-- statement:
--   For a labelled interaction with Hermitian terms, a block $B$ and $\beta>0$, the map $\mathcal K_B$ of (3.14) is a Lindblad generator ($e^{t\mathcal K_B}$ is a channel for every $t\ge0$), its dynamics preserves $\sigma_\beta=e^{-\beta H}/\mathrm{Tr}\,e^{-\beta H}$ ($\mathcal K_B(\sigma_\beta)=0$), and it is KMS reversible: its Heisenberg adjoint is self-adjoint for
--
--   $$
--   \langle A,C\rangle_{\sigma_\beta}=\mathrm{Tr}\big(A^*\sigma_\beta^{1/2}C\sigma_\beta^{1/2}\big).
--   $$
--
--   Consequently every $\Phi_B(T)=e^{T\mathcal K_B}$, $T\ge0$, is a channel with $\Phi_B(T)(\sigma_\beta)=\sigma_\beta$ whose Heisenberg adjoint is KMS self-adjoint.
--
--   This makes the block updates legitimate Gibbs samplers: each one fixes the global Gibbs state exactly.
--
--   Differences from the source:
--   - generalization: a Hamiltonian (2.1) with $2\le|X_\alpha|\le k$, $\operatorname{diam}X_\alpha\le r$, each site in at most $\nu$ supports → any finite labelled family $(h_\alpha, X_\alpha)$ with Hermitian terms supported on $X_\alpha$ and Hermitian on-site terms (`Interaction.IsValid`); reason: the statement and its proof do not use the bookkeeping bounds; every Hamiltonian (2.1) is such a family
--   - encoding: $O_B(u)$, the solution of (3.6) on $[0,1]$ → the solution on all of $\mathbb R$ chosen by `Classical.epsilon` (entrywise derivatives); reason: the linear ODE has continuous coefficients, so the global solution exists, is unique, and restricts to the paper's
--   - encoding: operators on a region $U$, partial traces $\mathrm{Tr}_S$, marginals and restricted Gibbs states acting on the subsystem → full-space matrices on $\prod_i \mathrm{Fin}\,d_i$: $A\otimes\mathbb 1$, `ptr S X` $=\mathbb 1_S\otimes\mathrm{Tr}_S X$, `gibbs β (hamOn I Ω)` $=\sigma^\Omega_\beta\otimes\mathbb 1/\dim$; reason: the paper extends operators by the identity in full-system expressions (p.10); norms, traces of products and covariances are unchanged
--   - encoding: "Lindblad generator" → $e^{t\mathcal K_B}$ is a channel for every $t\ge0$; reason: the paper's definition (§2.2, p.12)
--   - encoding: "preserves $\sigma_\beta$" → $\mathcal K_B(\sigma_\beta)=0$ and $\Phi_B(T)(\sigma_\beta)=\sigma_\beta$ for $T\ge0$; reason: the two forms of the paper's claim
--   - reading: local dimensions $2\le d_i\le d$ (standing) → local dimensions $d_i\ge2$; reason: the upper bound $d$ plays no role
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Proposition 3.4, p.19

import Mathlib
import Definitions.Def_QDSGibbs_blockChannel

open scoped Matrix

namespace QDSGibbs

/-- **Proposition 3.4 (Gibbs preservation and KMS detailed balance)** (arXiv:2610.03578, held file
sha256 ede55815…, Proposition 3.4, p.19). The map `K_B` of (3.14) is a Lindblad generator; its
dynamics preserves `σ_β = e^{−βH}/Tr e^{−βH}` and is KMS reversible: its Heisenberg adjoint is
self-adjoint for `⟨A, C⟩_{σ_β} = Tr(A^* σ_β^{1/2} C σ_β^{1/2})`. Every `Φ_B(T)` is consequently a
Gibbs-preserving, KMS-reversible channel.

**Formalization Note** General labelled interaction, any block `B`, `β > 0`; `K_B = blockGen β I B
univ`. "Lindblad generator" is the paper's definition (§2.2, p.12): `e^{tK_B}` is a channel for every
`t ≥ 0`. "Preserves `σ_β`" is `K_B(σ_β) = 0` together with `e^{tK_B}(σ_β) = σ_β`. KMS reversibility
of a map `F` is `⟨A, F^*(C)⟩_σ = ⟨F^*(A), C⟩_σ` for all operators `A, C`, with `F^* = heisAdj F`; it is
stated for `K_B` and for each `Φ_B(T)`, `T ≥ 0`. -/
theorem proposition_3_4 {N : ℕ} (d : Fin N → ℕ) (hd : ∀ i, 2 ≤ d i) (I : Interaction d)
    (hI : I.IsValid) (B : Finset (Fin N)) (β : ℝ) (hβ : 0 < β) :
    (∀ t : ℝ, 0 ≤ t → IsChannel (sexp (blockGen β I B Finset.univ) t)) ∧
    blockGen β I B Finset.univ (gibbs β (ham I)) = 0 ∧
    (∀ A C : Op d, kmsInner (gibbs β (ham I)) A (heisAdj (blockGen β I B Finset.univ) C) =
      kmsInner (gibbs β (ham I)) (heisAdj (blockGen β I B Finset.univ) A) C) ∧
    ∀ T : ℝ, 0 ≤ T →
      IsChannel (blockChannel β I B Finset.univ T) ∧
      blockChannel β I B Finset.univ T (gibbs β (ham I)) = gibbs β (ham I) ∧
      ∀ A C : Op d, kmsInner (gibbs β (ham I)) A (heisAdj (blockChannel β I B Finset.univ T) C) =
        kmsInner (gibbs β (ham I)) (heisAdj (blockChannel β I B Finset.univ T) A) C := by sorry

end QDSGibbs
