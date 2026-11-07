-- Prove2me | Theorems.Thm_SelfCorrect3D_Memory_homological_perturbation_lemma
-- name    : SelfCorrect3D.Memory.homological_perturbation_lemma
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:31:56.98434+00:00
-- url     : https://prove2.me/theorems/d21b3418-b0b0-4fa5-bd2a-814f1cd16f87
-- title:
--   Appendix A, Eqs. (244)–(247) — homological perturbation lemma over $\mathbb F_2$
-- statement:
--   Let $(C,d)$ and $(H,d_H)$ be complexes over $\mathbb F_2$ ($d^2=0$, $d_H^2=0$), let $i:H\to C$ and $p:C\to H$ be chain maps and $h:C\to C$ a linear map with
--
--   1. $pi=\mathrm{id}_H$, 2. $ip=\mathrm{id}_C+hd+dh$, 3. $hi=0$, 4. $ph=0$, 5. $h^2=0$.
--
--   Let $\delta$ be a perturbation with $(d+\delta)^2=0$ and $(h\delta)^N=0$ for some $N$. Put $\Sigma=\sum_{k\ge0}(\delta h)^k\delta$ and
--
--   $$d_H'=d_H+p\Sigma i,\qquad i'=i+h\Sigma i,\qquad p'=p+p\Sigma h,\qquad h'=h+h\Sigma h.$$
--
--   Then $(d_H')^2=0$, $i'$ and $p'$ are chain maps between $(H,d_H')$ and $(C,d+\delta)$, and conditions 1–5 hold for $(i',p',h')$ with $d$ replaced by $d+\delta$: $(H,d_H')$ is again a deformation retract of $(C,d+\delta)$.
--
--   The lemma is used to show that the codes keep one logical qubit through the construction (eq. (40)).
--
--   Differences from the source:
--   - generalization: graded chain complexes over F2 with h : C → C[−1] → F2-modules and linear maps with no grading; reason: the identities do not use the grading and over F2 there are no signs; a graded complex is the special case of the direct sum with degree-respecting maps
--   - encoding: a suitable smallness condition on δ; Σ = Σ_{k=0}^∞ (δh)^k δ → (h∘δ)^N = 0 and Σ = Σ_{k=0}^N (δh)^k δ; reason: the smallness condition of eq. (33) ("(h d_pert)^N = 0"); it gives (δh)^{N+1} = δ(hδ)^N h = 0, so the finite sum is the whole series
--   - reading: (H, d′_H) is again a deformation retract of (C, d′) → (d′_H)² = 0, i′ and p′ chain maps for d′_H and d + δ, and conditions 1–5 for (i′, p′, h′, d + δ); reason: the appendix's deformation-retract data consist of complexes, chain maps i, p and h satisfying 1–5 (p. 94); it verifies 1–5 and (d′_H)² = 0 in eqs. (248)–(274)
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, Appendix A, eqs. (244)–(247), pp. 94–95; §2.3.1, eqs. (30)–(33), pp. 14–15

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_hplSigma

namespace SelfCorrect3D.Memory

/-- **Homological perturbation lemma.** Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943, Appendix A,
pp. 94–95, eqs. (244)–(247) (also §2.3.1, eqs. (30)–(33), pp. 14–15).

Let `(C, d)`, `(H, d_H)` be complexes (`d² = 0`, `d_H² = 0`) over `𝔽₂`, `i : H → C`, `p : C → H`
chain maps and `h : C → C` with (1) `pi = id_H`, (2) `ip = id_C + hd + dh`, (3) `hi = 0`,
(4) `ph = 0`, (5) `h² = 0`. Let `δ` be a perturbation with `(d + δ)² = 0` and `(hδ)^N = 0`. With
`Σ = Σ_k (δh)^k δ`, `d′_H = d_H + pΣi`, `i′ = i + hΣi`, `p′ = p + pΣh`, `h′ = h + hΣh`:
`(d′_H)² = 0`, `i′`, `p′` are chain maps between `(H, d′_H)` and `(C, d + δ)`, and conditions
(1)–(5) hold for `(i′, p′, h′, d + δ)`.

**Formalization Note.** Ungraded: `C`, `H` are `𝔽₂`-modules and all maps are linear
endomorphisms/maps; the identities do not use the grading, and over `𝔽₂` there are no signs. The
smallness condition is the nilpotence `(hδ)^N = 0` of eq. (33), under which `hplSigma δ h N` is the
whole series (246). -/
theorem homological_perturbation_lemma {C H : Type} [AddCommGroup C] [Module (ZMod 2) C]
    [AddCommGroup H] [Module (ZMod 2) H]
    (d δ h : C →ₗ[ZMod 2] C) (dH : H →ₗ[ZMod 2] H) (i : H →ₗ[ZMod 2] C) (p : C →ₗ[ZMod 2] H)
    (N : ℕ)
    (hd : d ∘ₗ d = 0) (hdH : dH ∘ₗ dH = 0)
    (hi_chain : d ∘ₗ i = i ∘ₗ dH) (hp_chain : dH ∘ₗ p = p ∘ₗ d)
    (h1 : p ∘ₗ i = LinearMap.id) (h2 : i ∘ₗ p = LinearMap.id + h ∘ₗ d + d ∘ₗ h)
    (h3 : h ∘ₗ i = 0) (h4 : p ∘ₗ h = 0) (h5 : h ∘ₗ h = 0)
    (hpert : (d + δ) ∘ₗ (d + δ) = 0) (hsmall : (h ∘ₗ δ) ^ N = 0) :
    let S := hplSigma δ h N
    let dH' := dH + p ∘ₗ S ∘ₗ i
    let i' := i + h ∘ₗ S ∘ₗ i
    let p' := p + p ∘ₗ S ∘ₗ h
    let h' := h + h ∘ₗ S ∘ₗ h
    dH' ∘ₗ dH' = 0 ∧ (d + δ) ∘ₗ i' = i' ∘ₗ dH' ∧ dH' ∘ₗ p' = p' ∘ₗ (d + δ) ∧
      p' ∘ₗ i' = LinearMap.id ∧ i' ∘ₗ p' = LinearMap.id + h' ∘ₗ (d + δ) + (d + δ) ∘ₗ h' ∧
      h' ∘ₗ i' = 0 ∧ p' ∘ₗ h' = 0 ∧ h' ∘ₗ h' = 0 := by sorry

end SelfCorrect3D.Memory
