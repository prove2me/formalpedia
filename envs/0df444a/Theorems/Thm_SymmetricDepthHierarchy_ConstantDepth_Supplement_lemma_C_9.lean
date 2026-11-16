-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_lemma_C_9
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.lemma_C_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:14:14.706205+00:00
-- url     : https://prove2.me/theorems/e4187b61-2a7d-4cf8-ae81-0dd4509c70eb
-- title:
--   Lemma C.9 — Relational structures give separating weighted matrices
-- statement:
--   Let K be a characteristic-zero field, m,K_0,q_0,n,N>=1, N>=(n+1)^m, and let A,B have n elements over one finite vocabulary of arity at most m. Suppose A,B are not C_(K_0)^(q_0)-equivalent. One pair M,Mprime of N-by-N matrices and one pattern F satisfy the distinction below and simultaneously the equality clause for every pattern Fprime and every K,Delta>=1 meeting the stated width and equivalence conditions.
--
--   $$
--   \operatorname{fw}_{q_0+1}(F)\le K_0,\quad\operatorname{hom}_{F,N}(M)\ne\operatorname{hom}_{F,N}(M\prime),\qquad A\equiv_{C_{mK}^{mK\Delta}}B\Rightarrow\operatorname{hom}_{F\prime,N}(M)=\operatorname{hom}_{F\prime,N}(M\prime)\text{ if }\operatorname{fw}_\Delta(F\prime)\le K-1.
--   $$
--
--   This result supports Theorem C.10; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
--   - encoding: finite relational structures in the positive-arity vocabulary convention used by the incidence tuple range s in [m] → finite positive-arity relation-symbol types and recursively evaluated reusable-register counting formulas; reason: this implements the stated relational setting independently of homomorphism counts; empty vocabularies and empty universes are retained
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 46 (PDF p. 49), Lemma C.9; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Logic

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem lemma_C_9 (K : Type) [Field K] [CharZero K]
    (τ : Vocabulary) (m k₀ q₀ n N : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k₀) (hq : 1 ≤ q₀)
    (hn : 1 ≤ n) (hN : 1 ≤ N) (hsize : (n+1)^m ≤ N)
    (harity : ∀ R, τ.arity R ≤ m) (A B : RelStructure τ)
    (hA : Fintype.card A.U = n) (hB : Fintype.card B.U = n)
    (hdiff : ¬ countingEquiv A B k₀ q₀) :
    ∃ M M' : Matrix (Fin N) (Fin N) K, ∃ F : Pattern,
      FWLe F.graph (q₀+1) k₀ ∧
      MvPolynomial.eval (fun ij => M ij.1 ij.2) (F.homPoly K N) ≠
        MvPolynomial.eval (fun ij => M' ij.1 ij.2) (F.homPoly K N) ∧
      ∀ (F' : Pattern) (k Δ : ℕ), 1 ≤ k → 1 ≤ Δ → FWLe F'.graph Δ (k-1) →
        countingEquiv A B (m*k) (m*k*Δ) →
        MvPolynomial.eval (fun ij => M ij.1 ij.2) (F'.homPoly K N) =
          MvPolynomial.eval (fun ij => M' ij.1 ij.2) (F'.homPoly K N) := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
