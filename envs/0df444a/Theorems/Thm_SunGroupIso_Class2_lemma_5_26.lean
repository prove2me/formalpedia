-- Prove2me | Theorems.Thm_SunGroupIso_Class2_lemma_5_26
-- name    : SunGroupIso.Class2.lemma_5_26
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:08:52.980024+00:00
-- url     : https://prove2.me/theorems/4e833d21-24fb-436a-8c6c-441e840756a1
-- title:
--   Lemma 5.26 — every matching extended vector's highest-digit matrix lies in the orbit Ψ
-- statement:
--   Let $(z,Y,g,F,\rho)$ be a group restriction (positive parameters $\zeta,\gamma,\kappa,\tau,\delta$, with $\tau\ge2$, $\delta+1\le\tau$ and $p\le\mathrm{ord}(z_i)$) of a finite class-2 $p$-group $G$, $\vec a$ an extended vector of it, $\Gamma_1$ a finite list of invertible matrices generating exactly the normalized isometries ($Q[m,m]=1$) of the doubling of the Matrix Tuple Construction of $\vec a$, $\Gamma$ the generator list of §5.5 and $\Psi$ the least set containing $\theta_{\vec x}$ and closed under the update rule (12) of every generator in $\Gamma$. For every extended vector $\vec c$ of the same restriction matching $\vec a$, with augmented vector $\vec w\in G^L$, $\theta_{\vec w}\in\Psi$.
--
--   Differences from the source:
--   - generalization: a⃗ and Γ_1 the outputs of the Extended Vector Matching Algorithm → every extended vector a⃗ and every finite list Γ_1 generating the normalized isometry group of its doubled tuple; reason: the algorithm's outputs are such a pair, so the statement specializes to the source's
--   - reading: the standing assumption τ ≥ 2 of Section 5 (proof of Lemma 5.15) → hypothesis 2 ≤ τ; reason: FAITHFULNESS_TRAPS row 19; the other standing assumptions compare two restrictions and are trivial for one
--   - encoding: 'Repeat until Ψ does not change: for each θ ∈ Ψ and P ∈ Γ, add P(θ) to Ψ' → Ψ is the inductive closure InOrbit; reason: the loop computes exactly the least set containing θ_x⃗ closed under the update maps
--   - reading: §5.1 reindexing excludes trivial z_i, and §5.5 explicitly uses p^(δ+1) ≤ p^τ (PDF 29,52) → p ≤ ord(z_i) and δ+1 ≤ τ; reason: ensures L_k = ord(z_k)/p > 0 and the appended h_k have orders at most p^τ, exactly as in the construction
-- source:
--   Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Lemma 5.26, p. 52 (PDF p. 54)

import Mathlib
import Definitions.Def_SunGroupIso_Class2_MatrixTuple

set_option autoImplicit false

open scoped Classical commutatorElement

namespace SunGroupIso.Class2

open ExponomialAssortment.FPTAS (encodeNat)
open GroupIsoPoly (encPair cayley)

/-- **Lemma 5.26** (Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Lemma 5.26, p. 52, PDF p. 54). Let `a⃗` be an extended vector of a group restriction,
`Γ_1` a generating set of the normalized isometries (`Q[m,m] = 1`) of the doubling of its constructed tuple, `Γ`
the generator list of §5.5 and `Ψ` the orbit of `θ_x⃗` under the update rule (12). For every extended vector
`c⃗` matching `a⃗` for the same group restriction, with augmented vector `w⃗ ∈ G^L`, `θ_w⃗ ∈ Ψ`. -/
theorem lemma_5_26 {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G] (hG : IsPGroupClass2 p G)
    {ζ γ κ τ δ : ℕ} (r : Restriction G p ζ γ κ τ) (hr : IsRestriction p δ r) (hτ : 2 ≤ τ)
    (hδτ : δ + 1 ≤ τ) (hz : ∀ i, p ≤ orderOf (r.z i))
    {n : ℕ} (a : Fin n → G) (ha : IsExtVec r a)
    (Γ1 : List (GL (Fin (doubling (mtc r a)).size) (ZMod (p ^ τ))))
    (hΓ : (Subgroup.closure {P | P ∈ Γ1} : Set (GL (Fin (doubling (mtc r a)).size) (ZMod (p ^ τ)))) =
      normIsoSet (doubling (mtc r a)) (mtc r a).size)
    (c : Fin n → G) (hc : IsExtVec r c) (hm : Matches r c r a) :
    theta r a (augment δ r a c) ∈ Psi δ r a Γ1 := by sorry

end SunGroupIso.Class2
