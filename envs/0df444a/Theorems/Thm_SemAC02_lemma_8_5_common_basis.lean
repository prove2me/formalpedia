-- Prove2me | Theorems.Thm_SemAC02_lemma_8_5_common_basis
-- name    : SemAC02.lemma_8_5_common_basis
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:29:14.765724+00:00
-- url     : https://prove2.me/theorems/9b455fef-39b2-45d7-a191-2ddf43481c62
-- title:
--   Lemma 8.5 — common monomial basis
-- statement:
--   Let $g_0:\{0,1\}^m\to\{0,1\}$ be antitone, $g_1(X)=g_0(\overline X)$, $L=\{S\subseteq[m]:g_0(\mathbf 1_S)=1\}$, $\Omega_0=\{X:g_0(X)=1\}$ and $\Omega_1=\{X:g_1(X)=1\}$. The monomials $x_S=\prod_{j\in S}x_j$, $S\in L$, restricted to $\Omega_b$, form a basis of the space $\mathbb F_2^{\Omega_b}$ of all functions $\Omega_b\to\mathbb F_2$, for both $b=0$ and $b=1$.
--
--   A single family of monomials thus represents functions on both sets where a lifted literal has a definite value, which is what makes coefficients in the base variables well defined.
--
--   Differences from the source:
--   - generalization: g₀ = g, the gadget circuit of §8.1 (AND-rooted, depth ≤ d + 1, antitone, g(X) ∧ g(X̄) = 0) → any antitone Boolean function g₀ : {0,1}^m → {0,1}; reason: the proof uses only antitonicity (L downward closed); the gadget's evaluation is such a function
--   - encoding: basis of F₂^{Ω_b} → LinearIndependent family of restrictions and span = ⊤; reason: definition of a basis
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Lemma 8.5, p.64 (PDF p.66)

import Mathlib
import Definitions.Def_AC02Frege_ML
import Definitions.Def_SemAC02_Ble
import Definitions.Def_SemAC02_multiplierSpace

namespace SemAC02

/-- **Lemma 8.5 (Common monomial basis)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Lemma 8.5, p.64): with
`L = {S ⊆ [m] : g₀(1_S) = 1}`, `Ω₀ = {X : g₀(X) = 1}` and `Ω₁ = {X : g₁(X) = 1}`,
`g₁(X) = g₀(X̄)`, the monomials `x_S = ∏_{j∈S} x_j`, `S ∈ L`, give a basis of both `𝔽₂^{Ω₀}`
and `𝔽₂^{Ω₁}`.

**Formalization Note** Stated for every antitone Boolean function `g₀` on `{0,1}^m` (the
paper's `g₀ = g` from §8.1 is one). "Basis" is linear independence of the restrictions of the
`x_S` to `Ω_b` together with spanning all functions `Ω_b → 𝔽₂`. -/
theorem lemma_8_5_common_basis {m : ℕ} (g₀ : (Fin m → Bool) → Bool) (hg₀ : Antitone g₀) :
    (LinearIndependent (ZMod 2)
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ X = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1)) ∧
      Submodule.span (ZMod 2) (Set.range
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ X = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1))) = ⊤) ∧
    (LinearIndependent (ZMod 2)
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ (fun j => !X j) = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1)) ∧
      Submodule.span (ZMod 2) (Set.range
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ (fun j => !X j) = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1))) = ⊤) := by sorry

end SemAC02
