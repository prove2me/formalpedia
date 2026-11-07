-- Prove2me | Theorems.Thm_TightQLB_lemma_4_1
-- name    : TightQLB.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:02:37.93481+00:00
-- url     : https://prove2.me/theorems/c355a1b5-88ed-4685-b550-cb7256c57d28
-- title:
--   Lemma 4.1 — identities for the removal operators
-- statement:
--   Let $x,z\in\{0,1\}^n$ and let $\Phi\in\mathcal F$. Then:
--
--   1. $\sum_wb_w^\dagger b_w=D$;
--   2. $b_zb_z^\dagger-b_z^\dagger b_z=I-\frac2ND$;
--   3. $\displaystyle\sum_w\bigl\|(b_w^2\mathcal X_x-\mathcal X_xb_w^2)\Phi\bigr\|^2=\frac4N\langle\Phi,(D-n_x)\Phi\rangle$.
--
--   Part 3 says that the commutator of $b_w^2$ with multiplication by $f(x)$, summed over $w$, has squared norm $4/N$ times the number of recorded points other than $x$, weighted by $\|\Phi_S\|^2$.
--
--   Differences from the source:
--   - generalization: "Throughout, n ≥ 1" (p. 13) → every n : ℕ, with no hypothesis on n; reason: the argument does not use n ≥ 1, and the instances with n ≥ 1 are the source's statement
--   - encoding: H = A ⊗ E and the space F of functions f ↦ Φ(f) ∈ H → any finite index type H, with Φ : (Qubits n → Bool) → H → ℂ; reason: coordinates in a finite orthonormal basis
--   - encoding: the operator identities (i) and (ii) → the identities applied to an arbitrary Φ; reason: two operators are equal exactly when they agree on every Φ
--   - encoding: ⟨Φ, (D − n_x)Φ⟩ in (iii) → its real part; reason: the form is real, since D − n_x is a sum of projections
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), Lemma 4.1, p. 22 (PDF p. 25)

import Mathlib
import Definitions.Def_TightQLB_Recording
open QAlgorithms

namespace TightQLB

/-- **Lemma 4.1 (Identities for the removal operators)**, p.22 (PDF p.25).

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

"Let x, z ∈ {0,1}^n and let Φ ∈ F. Then (i) Σ_w b_w† b_w = D; (ii) b_z b_z† − b_z† b_z = I − (2/N) D;
(iii) Σ_w ‖(b_w² 𝒳_x − 𝒳_x b_w²)Φ‖² = (4/N) ⟨Φ, (D − n_x)Φ⟩."

**Formalization Note.** (i) and (ii) are stated applied to an arbitrary `Φ ∈ F`, which is the
operator identity. In (iii) the right side is the real part of `⟨Φ, (D − n_x)Φ⟩` (the form is real,
`D − n_x` being a sum of projections). `H` is an arbitrary finite type; `n ≥ 1` is not needed. -/
theorem lemma_4_1 {n : ℕ} {H : Type} [Fintype H] (x z : Qubits n) (Φ : Fn n H) :
    (∑ w, bOpAdj w (bOp w Φ) = Dop Φ) ∧
    (bOp z (bOpAdj z Φ) - bOpAdj z (bOp z Φ) = Φ - (2 / (2 : ℝ) ^ n) • Dop Φ) ∧
    (∑ w, nsq (bOp w (bOp w (mulX x Φ)) - mulX x (bOp w (bOp w Φ))) =
      4 / (2 : ℝ) ^ n * (ip Φ (Dop Φ - numOp x Φ)).re) := by sorry

end TightQLB
