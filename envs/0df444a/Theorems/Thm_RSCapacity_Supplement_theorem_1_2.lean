-- Prove2me | Theorems.Thm_RSCapacity_Supplement_theorem_1_2
-- name    : RSCapacity.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:28:00.706133+00:00
-- url     : https://prove2.me/theorems/e5146121-fb2c-4ee2-9576-bcf361df6d73
-- title:
--   Theorem 1.2 (Fixed-slack capacity-radius curve MCA)
-- statement:
--   Fix $\gamma\in(0,1)$ and an integer $\ell\ge1$. There are effective constants $C=C(\gamma,\ell)>0$ and $n_0=n_0(\gamma,\ell)$ such that the following holds. Let $n\ge n_0$, let $q\ge n$ be prime, let $D=\{\alpha_1,\dots,\alpha_n\}\subseteq\mathbb F_q$ consist of $n$ distinct points, and let $C=\mathrm{RS}_{\mathbb F_q}(D,k)$ with $1\le k\le(1-\gamma)n$. For arbitrary coefficient words $f_0,\dots,f_\ell\in\mathbb F_q^n$ and every radius $0\le\rho\le 1-k/n-\gamma$,
--   $$\bigl|\mathrm{Bad}^{(\ell)}_{C,\rho}(f_0,\dots,f_\ell)\bigr|\le n^{C}.$$
--   In particular, for lines ($\ell=1$),
--   $$\mathrm{err}_{\mathrm{MCA}}(C,\rho)\le\frac{n^{C(\gamma,1)}}{q}.$$
--
--   This is the paper's mutual-correlated-agreement (proximity-gap) theorem at radii up to the capacity curve $1-k/n-\gamma$: the number of exceptional curve parameters is polynomial in $n$, independently of $q$.
--
--   **Formalization Note** $\mathbb F_q$ is `ZMod q` with `Fact q.Prime`; $D$ is an injective map $\alpha:[n]\to\mathbb F_q$. The constants are functions of $\ell$ chosen after $\gamma$ and before all other data; the "for lines" clause uses the same constant $C(1)$ and threshold $n_0(1)$ as the $\ell=1$ bound. $n^C$ is a real power.
--
--   Differences from the source:
--   - encoding: effective constants C(γ, ℓ), n_0(γ, ℓ) → functions C (real-valued) and n₀ (natural-valued) of ℓ, chosen after γ; reason: the same as choosing them for each ℓ, and it lets the line clause use C(γ, 1)
--   - encoding: prime field 𝔽_q and D ⊆ 𝔽_q with n distinct points → ZMod q with Fact q.Prime and an injective map α from Fin n to ZMod q; reason: Lean convention, same instances
--   - encoding: A_ρ = n − ⌊ρn⌋ → n − Nat.floor (ρ n) in ℕ; reason: 0 ≤ ρ ≤ 1 here, so Nat.floor is the floor and the subtraction does not truncate
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Theorem 1.2, p.2 (PDF 4); Definition 3.3, p.12 (PDF 14); proof in §8.2, pp.32–33 (PDF 34–35)

import Mathlib
import Definitions.Def_RSCapacity_Supplement_Defs

open Polynomial

set_option autoImplicit false

namespace RSCapacity.Supplement

/-- **Theorem 1.2 (Fixed-slack capacity-radius curve MCA).** Jeronimo, arXiv:2609.05870 (held
version of November 1, 2026, sha256 9a0069bd…), Theorem 1.2, p.2 (PDF 4); Definition 3.3, p.12
(PDF 14); proof in §8.2, pp.32–33 (PDF 34–35). Fix γ ∈ (0, 1) and an integer ℓ ≥ 1. There are
effective constants C = C(γ, ℓ) > 0, n_0 = n_0(γ, ℓ) such that the following holds. Let n ≥ n_0,
let q ≥ n be prime, let D = {α_1, …, α_n} ⊆ 𝔽_q have n distinct points, and let
C = RS_{𝔽_q}(D, k), 1 ≤ k ≤ (1 − γ)n. For arbitrary f_0, …, f_ℓ ∈ 𝔽_q^n and every
0 ≤ ρ ≤ 1 − k/n − γ, one has |Bad^{(ℓ)}_{C,ρ}(f_0, …, f_ℓ)| ≤ n^C. In particular, for lines,
err_MCA(C, ρ) ≤ n^{C(γ,1)}/q.

**Formalization Note.** 𝔽_q is `ZMod q` with `[Fact q.Prime]`; D is an injective
`α : Fin n → ZMod q`; the code C is given by (α, k). The constants are functions `C n₀ : ℕ → _`
of ℓ, chosen after γ and before n, q, α, k, ρ and the words (this is "∀ ℓ ∃ C(γ, ℓ), n₀(γ, ℓ)").
C(ℓ) is a positive real and n^C is the real power. The "for lines" clause is the conjunct under
`ℓ = 1`, with the same constant C 1 and threshold n₀ 1 as the ℓ = 1 bound. ρ and k/n are real. -/
theorem theorem_1_2 (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ (C : ℕ → ℝ) (n₀ : ℕ → ℕ), (∀ ℓ : ℕ, 1 ≤ ℓ → 0 < C ℓ) ∧
      ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ (n q : ℕ) [Fact q.Prime], n₀ ℓ ≤ n → n ≤ q →
      ∀ α : Fin n → ZMod q, Function.Injective α →
      ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ (1 - γ) * n →
      ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 - (k : ℝ) / n - γ →
        (∀ f : Fin (ℓ + 1) → Fin n → ZMod q, ((bad α k f ρ).ncard : ℝ) ≤ (n : ℝ) ^ C ℓ) ∧
        (ℓ = 1 → errMCA α k ρ ≤ (n : ℝ) ^ C 1 / q) := by sorry

end RSCapacity.Supplement
