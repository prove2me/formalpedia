-- Prove2me | Theorems.Thm_SelfCorrect3D_Memory_peierls_contains_coboundary
-- name    : SelfCorrect3D.Memory.peierls_contains_coboundary
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:30:50.884736+00:00
-- url     : https://prove2.me/theorems/af6255d5-04dc-4416-8020-a1cae8f2a068
-- title:
--   §5.4, Eqs. (218)–(220) — Peierls estimate $\mathbb P(\tau\subseteq\sigma)\le e^{-\beta|\tau|}$
-- statement:
--   Let $\delta:\mathbb F_2^n\to\mathbb F_2^m$ be linear, $B=\operatorname{im}\delta$ the space of coboundaries, and consider the Gibbs distribution $\mathbb P(\sigma)=e^{-\beta|\sigma|}/Z$ on $B$, $Z=\sum_{\sigma\in B}e^{-\beta|\sigma|}$, where $|\sigma|$ is the Hamming weight. For every $\tau\in B$ and every $\beta\in\mathbb R$,
--
--   $$\mathbb P(\tau\subseteq\sigma)=\frac{1}{Z}\sum_{\sigma\in B:\ \tau\subseteq\sigma}e^{-\beta|\sigma|}\le e^{-\beta|\tau|},$$
--
--   where $\tau\subseteq\sigma$ means that the support of $\tau$ is contained in that of $\sigma$.
--
--   This is the energy estimate of the Peierls argument behind Theorem 5.13.
--
--   Differences from the source:
--   - generalization: β > β_c → every real β; reason: the estimate holds termwise for every β; specializes to β > β_c
--   - generalization: the 2-coboundaries B²(C(2k)) of the paper's cochain complex → the range of any F2-linear map δ; reason: B²(C(2k)) = im δ¹ is a special case
--   - encoding: τ2k ⊆ σ2k → support of τ contained in support of σ; reason: syndromes are sets of violated checks
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, §5.4, proof of Theorem 5.13, eqs. (218)–(220), p. 66; Σ_{2k}(β), p. 61

import Mathlib

namespace SelfCorrect3D.Memory

open Classical in
/-- **Peierls estimate (eqs. (218)–(220)).** Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943, §5.4, proof of
Theorem 5.13, eqs. (218)–(220), p. 66; the distribution `Σ_{2k}(β)` of p. 61:
`P(σ) = e^{−β|σ|}/Z`, `Z = Σ_{σ ∈ B²} e^{−β|σ|}`.

For a linear map `δ : 𝔽₂ⁿ → 𝔽₂^m` with coboundary space `B = im δ`, every `τ ∈ B` and every real
`β`, the Gibbs probability on `B` that `σ` contains `τ` is at most `e^{−β|τ|}`:
`(Σ_{σ ∈ B, τ ⊆ σ} e^{−β|σ|}) / (Σ_{σ ∈ B} e^{−β|σ|}) ≤ e^{−β|τ|}`.

**Formalization Note.** `|·|` is the Hamming weight; "τ ⊆ σ" is containment of supports. The
paper uses `β > β_c`; the statement holds for every real `β` (generalization). `δ` stands for the
paper's `δ¹`, so `B` is the space of 2-coboundaries. -/
theorem peierls_contains_coboundary {n m : ℕ}
    (δ : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) (τ : Fin m → ZMod 2)
    (hτ : τ ∈ LinearMap.range δ) (β : ℝ) :
    (∑ σ ∈ Finset.univ.filter (fun σ : Fin m → ZMod 2 =>
          σ ∈ LinearMap.range δ ∧ ∀ i, τ i ≠ 0 → σ i ≠ 0),
        Real.exp (-β * hammingNorm σ)) /
      (∑ σ ∈ Finset.univ.filter (fun σ : Fin m → ZMod 2 => σ ∈ LinearMap.range δ),
        Real.exp (-β * hammingNorm σ)) ≤
      Real.exp (-β * hammingNorm τ) := by sorry

end SelfCorrect3D.Memory
