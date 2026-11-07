-- Prove2me | Theorems.Thm_QMAPlusGap_lemma_A_3
-- name    : QMAPlusGap.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:09:29.700441+00:00
-- url     : https://prove2.me/theorems/bc415232-9a2f-4606-9af9-735bc313627c
-- title:
--   Lemma A.3 — $\|\Pi_S\rho_\ell\Pi_S\|_2^2\le\operatorname{Tr}[(Q\rho_1Q)^2]+\frac{2+2\ell(\ell-1)}{m}$
-- statement:
--   Let $\Gamma_m$ be a density operator supported on $\mathrm{Sym}^m(\mathcal H)$ with reduced states $\rho_\ell$ and $\rho_1$ on $\ell$ registers and one register, $1\le\ell\le m$. Let $P$ be an orthogonal projector and $Q=I-P$. For $S=(S_1,\dots,S_\ell)\in\{P,Q\}^\ell$ write $\Pi_S=S_1\otimes\cdots\otimes S_\ell$. If $S\ne(P,\dots,P)$, then
--   $$
--   \|\Pi_S\rho_\ell\Pi_S\|_2^2\ \le\ \operatorname{Tr}\big[(Q\rho_1Q)^2\big]+\frac{2+2\ell(\ell-1)}{m}.\tag{A.4}
--   $$
--
--   Each block of $\rho_\ell$ that touches the low-eigenvalue part $Q$ has small Hilbert–Schmidt mass; summing over the $2^\ell-1$ such blocks gives Lemma 13.
--
--   Differences from the source:
--   - encoding: S ∈ {P, Q}^ℓ; Tr[(Qρ₁Q)²] → S : Fin ℓ → Bool (true = P); the real part of the trace; reason: same patterns; the trace of the square of a Hermitian operator is real
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma A.3, p.34

import Mathlib
import Definitions.Def_QMAPlusGap_IsSymSupported
import Definitions.Def_QMAPlusGap_reduce
import Definitions.Def_OptimalSpectrum_Entangled_kronFamily
import Definitions.Def_QMAPlusGap_IsOrthProj
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_hsNorm

set_option autoImplicit false

open scoped MatrixOrder ComplexOrder
open MeasureTheory Filter

namespace QMAPlusGap

/-- **Lemma A.3**, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), p.34: "Let Γ_m be a density operator supported on Sym^m(H), and let ρ_ℓ and ρ_1 be its
reduced states on ℓ registers and one register, respectively, where 1 ≤ ℓ ≤ m. Let P be an orthogonal projector
and set Q = I − P. For S = (S_1, …, S_ℓ) ∈ {P, Q}^ℓ, write Π_S = S_1 ⊗ ⋯ ⊗ S_ℓ. If S ≠ (P, …, P), then
∥Π_S ρ_ℓ Π_S∥₂² ≤ Tr[(Qρ_1Q)²] + (2 + 2ℓ(ℓ − 1))/m. (A.4)"

**Formalization Note** A pattern `S` is `Fin ℓ → Bool` (`true` = `P`, `false` = `Q`); `ρ_1 = reduceOne Γ`; the
trace `Tr[(Qρ_1Q)²]` is real and its real part is taken. -/
theorem lemma_A_3 {ι : Type} [Fintype ι] [DecidableEq ι] (m ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓm : ℓ ≤ m)
    (Γ : Matrix (Fin m → ι) (Fin m → ι) ℂ) (hΓ : WildeQIT.IsDensityOperator Γ) (hΓs : IsSymSupported Γ)
    (P : Matrix ι ι ℂ) (hP : IsOrthProj P) (S : Fin ℓ → Bool) (hS : S ≠ fun _ => true) :
    WildeQIT.hsNorm (OptimalSpectrum.Entangled.kronFamily (fun r => if S r then P else 1 - P) * reduce ℓ Γ *
        OptimalSpectrum.Entangled.kronFamily (fun r => if S r then P else 1 - P)) ^ 2 ≤
      (Matrix.trace (((1 - P) * reduceOne Γ * (1 - P)) ^ 2)).re +
        (2 + 2 * (ℓ : ℝ) * ((ℓ : ℝ) - 1)) / (m : ℝ) := by sorry

end QMAPlusGap
