-- Prove2me | Theorems.Thm_PinningSyncAudit_GeneralCoupling_lemma_2_8
-- name    : PinningSyncAudit.GeneralCoupling.lemma_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:51:20.583074+00:00
-- url     : https://prove2.me/theorems/da9fe47b-c9fe-4936-8d6e-e550c4a0443c
-- title:
--   Lemma 2.8 — strictly positive spectral-radius eigenvector
-- statement:
--   Let $N\ge1$ and let $A\in\mathbb R^{N\times N}$ be entrywise nonnegative and irreducible: no simultaneous permutation of rows and columns produces a zero upper-right block with both diagonal blocks nonempty. Let $\rho(A)$ be the largest modulus of a complex root of the characteristic polynomial of $A$. Then
--
--   $$
--   \det(\rho(A)I-A)=0,
--   \qquad
--   \exists x\in\mathbb R^N:\quad (\forall i,\ x_i>0)\ \text{and}\ Ax=\rho(A)x.
--   $$
--
--   Thus the spectral radius is itself a real eigenvalue with an eigenvector positive in every coordinate. This supplies the exact source interface used by Lemma 2.11. The two referenced Perron–Frobenius results supply a nonnegative nonzero eigenvector and its strict positivity, respectively, after translating their conventions. Neither one alone states this full source result. Their translation and the singleton zero case are proof obligations, not new hypotheses.
--
--   **Formalization Note** The first displayed clause is represented by the real characteristic polynomial having $\rho(A)$ as a root. For $N=1$ and $A=[0]$, the conclusion includes $\rho(A)=0$ and a positive scalar eigenvector.
--
--   Differences from the source:
--   - encoding: a positive-dimensional real square matrix, irreducible in Definition 2.4, with spectral radius the largest modulus of its complex eigenvalues → N > 0, indices Fin N, the published permutation-block predicate IsIrred, and specRad defined by characteristic roots; the eigenvalue clause is A.charpoly.IsRoot (specRad A); reason: these express the same matrix and eigenvalue notions; no positive-length irreducibility or positive spectral radius is assumed, so N = 1 and A = [0] remain covered
-- source:
--   Yu, Chen, Lü and Kurths, Synchronization via pinning control on general complex networks, SIAM J. Control Optim. 51(2) (2013), 1395–1416, https://doi.org/10.1137/100781699, p. 1400, Lemma 2.8; Definition 2.4 on p. 1399 (PDF pp. 6 and 5)

import Mathlib
import Definitions.Def_PinningSync_Strong_Setting
import Theorems.Thm_SaturatedNet_Uniqueness_proposition_2_i_ii
import Theorems.Thm_SaturatedNet_Uniqueness_proposition_2_iii_v

namespace PinningSyncAudit.GeneralCoupling

open Matrix

/-- Lemma 2.8, p. 1400 (PDF 6), in the source's permutation-block and
characteristic-root interfaces. The imported PF ingredients require bridges;
their positive-length irreducibility is not assumed here. In particular the
irreducible singleton zero matrix and zero spectral radius remain in scope. -/
theorem lemma_2_8 {N : ℕ} (hN : 0 < N)
    (A : Matrix (Fin N) (Fin N) ℝ)
    (hirr : PinningSync.Strong.IsIrred A) (hA : ∀ i j, 0 ≤ A i j) :
    A.charpoly.IsRoot (PinningSync.Strong.specRad A) ∧
      ∃ x : Fin N → ℝ, (∀ i, 0 < x i) ∧
        A *ᵥ x = (PinningSync.Strong.specRad A) • x := by sorry

end PinningSyncAudit.GeneralCoupling
