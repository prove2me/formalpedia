-- Prove2me | Theorems.Thm_RandProdExp_TwoSided_lemma_6_16
-- name    : RandProdExp.TwoSided.lemma_6_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:20:14.474058+00:00
-- url     : https://prove2.me/theorems/00276b50-530d-49f0-a6e0-0ea8b9dbf3ed
-- title:
--   Lemma 6.16 — a real sign witness yields $f_\sigma\in\mathbb Z[X]$ with $1\le|f_\sigma(\sigma)|\le N_M^{N_M/2}$, $\deg f_\sigma\le DN_M$, certifying injectivity
-- statement:
--   Let $D\ge1$, $n\ge2$, $M\subseteq[n]^D$, let $k_1,\dots,k_D$ be dimensions, and let $\sigma$ be a real sign witness for $(M,(k_i))$. Put $N_M=\dim U_M=\sum_{P=P(I,a)\in\mathcal P_\cap(M)}\prod_{i\in I}k_i$. There is a polynomial $f_\sigma\in\mathbb Z[X]$ in the indeterminates $X^{(i)}_{r,j}$ such that
--   $$1\le|f_\sigma(\sigma)|\le N_M^{N_M/2},\qquad \deg f_\sigma\le D\,N_M,$$
--   and such that, over any field $K$, every specialization $x$ of $X$ with $f_\sigma(x)\neq0$ makes $\bar\beta^x_M$ injective; if moreover every $x_i$ has full row rank, then the corestriction map $\tau_M$ of the row-space codes $\operatorname{Im}(x_i^\top)$ is injective. It is the integer certificate that carries injectivity from $\mathbb R$ to finite fields.
--
--   Differences from the source:
--   - encoding: standing assumption of §3.1 (p. 19): integers D ≥ 1 and n ≥ 2 → explicit hypotheses 1 ≤ D and 2 ≤ n; reason: stated once at the top of §3.1 for the whole paper; makes the anchor of a plane unique
--   - encoding: f_σ(σ), the value at the sign matrices → specialize (signsInt σ) f, an integer; reason: f_σ has integer coefficients and σ integer entries
--   - encoding: deg f_σ → MvPolynomial.totalDegree; reason: total degree, as in the proof (entries are monomials of degree ≤ D)
--   - encoding: 'β̄^x_M is the corestriction map τ_M of the row-space codes, so τ_M is injective' → if rank x_i = k_i for all i then tauMap M (rowSpace ∘ x) is injective; reason: the identification is an isomorphism (Lemma 4.8); its stated consequence, injectivity of τ_M, is what is formalized
--   - encoding: 'over any field' → every field K : Type; reason: Lean universe convention
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), p. 41, Lemma 6.16

import Mathlib
import Definitions.Def_RandProdExp_TwoSided_Grid
import Definitions.Def_RandProdExp_TwoSided_Codes
import Definitions.Def_RandProdExp_TwoSided_Diagram

namespace RandProdExp.TwoSided

/-- **Lemma 6.16** (p. 41). Let `M ⊆ [n]^D`, let `(k_i)` be dimensions and let `σ` be a real sign
witness for `(M, (k_i))`. Put `N_M = dim U_M = Σ_{P = P(I,a) ∈ P∩(M)} Π_{i ∈ I} k_i`. There is a
polynomial `f_σ ∈ ℤ[X]` with `1 ≤ |f_σ(σ)| ≤ N_M^{N_M/2}` and `deg f_σ ≤ D N_M` such that, over any
field, every specialization `x` of `X` with `f_σ(x) ≠ 0` makes `β̄^x_M` injective; if moreover every
`x_i` has full row rank, then the corestriction map `τ_M` of the row-space codes is injective.
(Standing assumptions of §3.1: `D ≥ 1`, `n ≥ 2`.) -/
theorem lemma_6_16 (D n : ℕ) (hD : 1 ≤ D) (hn : 2 ≤ n) (M : Set (Fin D → Fin n))
    (k : Fin D → ℕ) (σ : SignTuple k n) (hσ : IsRealSignWitness M σ) :
    ∃ f : MvPolynomial (Var k n) ℤ,
      1 ≤ |(specialize (signsInt σ) f : ℤ)| ∧
      ((|(specialize (signsInt σ) f : ℤ)| : ℤ) : ℝ) ≤ (dimUM M k : ℝ) ^ ((dimUM M k : ℝ) / 2) ∧
      f.totalDegree ≤ D * dimUM M k ∧
      ∀ (K : Type) [Field K] (x : (i : Fin D) → Matrix (Fin (k i)) (Fin n) K),
        specialize x f ≠ 0 →
          BarInjective M x ∧
            ((∀ i, (x i).rank = k i) → Function.Injective (tauMap M (fun i => rowSpace (x i)))) := by sorry

end RandProdExp.TwoSided
