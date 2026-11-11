-- Prove2me | Theorems.Thm_UnitalMIP_lemma_3_5
-- name    : UnitalMIP.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:39:59.349642+00:00
-- url     : https://prove2.me/theorems/2e3f3dca-5dfe-4f83-971f-8599fbfbe2c8
-- title:
--   Lemma 3.5 — rounding block approximants to POVMs at cost $15\nu$
-- statement:
--   Fix a game $G$, an integer $n\ge1$, and the resource state $\psi^{\otimes n}$ with $\psi_A=\psi_B=\mathbb 1/2$. Let $(Q^x)_x$, $(R^y)_y$ be block approximants on $(\mathbb C^2)^{\otimes n}$ with measurement elements $\mathcal Q$, $\mathcal R$ as in (21). If, for some $0\le\nu\le1$,
--
--   $$
--   \mathbb E_{x\sim p_X}\|(Q^x)^\dagger Q^x-\mathbb 1\|_2^2\le\nu^4,\qquad \mathbb E_{y\sim p_Y}\|(R^y)^\dagger R^y-\mathbb 1\|_2^2\le\nu^4,
--   $$
--
--   then there are POVM strategies $\mathcal A^\sharp$, $\mathcal B^\sharp$ on $(\mathbb C^2)^{\otimes n}$ with $|\mathrm{Val}_G(\mathcal Q,\mathcal R)-\mathrm{Val}_G(\mathcal A^\sharp,\mathcal B^\sharp)|\le15\nu$.
--
--   Rounding turns approximately normalized operators back into genuine measurements, closing the approximation chain.
--
--   **Formalization Note** $\psi$ is a two-qubit density matrix; both values are on $\psi^{\otimes n}$.
--
--   Differences from the source:
--   - encoding: $\mathbb E_{x\sim p_X}$, $\mathbb E_{y\sim p_Y}$ → $\sum_x p_X(x)(\cdot)$, $\sum_y p_Y(y)(\cdot)$ with the marginals (15); reason: same expectations
--   - encoding: $\psi^{\otimes n}$ → `tensorPow ψ n`: the same operator with Alice's $n$ registers collected first; reason: a permutation of tensor factors; Alice holds the first qubit of every copy, as in the source
--   - encoding: $\mathrm{Tr}[(A^x_a\otimes(B^y_b)^T)\psi]$ in the value (16), (22) → the real part of this trace; reason: the trace is real for the positive semidefinite families and states to which the source applies the formula
--   - generalization: the §1.1 standing assumption (“Throughout, let ψ be a fixed two-qubit state … and assume that its entries are computable in polynomial time”, p.4) → any two-qubit density matrix ψ with the stated properties, with no computability hypothesis; reason: the statement is purely analytic and holds for every such state; it specializes to the source's claim on every computable ψ
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Lemma 3.5, p.28

import Mathlib
import Definitions.Def_UnitalMIP_HasMaxMixedMarginals
import Definitions.Def_UnitalMIP_rhoMax
import Definitions.Def_UnitalMIP_omegaInf

open scoped Matrix

namespace UnitalMIP

/-- **Lemma 3.5** (Rounding; Dong, Jiang, Qin, Yao, Zhou, *A Dichotomy for MIP* in the Presence of Unital Noise*, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), p.28). Fix a game `G`, `n ≥ 1`, and the resource state `ψ^{⊗n}`
with `ψ_A = ψ_B = 𝟙/2`. Let `Q^x`, `R^y` be block approximants on `(ℂ²)^{⊗n}` and `𝒬`, `ℛ` their
measurement elements (21). If, for some `0 ≤ ν ≤ 1`,
`E_{x∼p_X} ‖(Q^x)†Q^x − 𝟙‖₂² ≤ ν⁴` and `E_{y∼p_Y} ‖(R^y)†R^y − 𝟙‖₂² ≤ ν⁴`, then there are POVM
strategies `𝒜♯`, `ℬ♯` on `(ℂ²)^{⊗n}` with `|Val_G(𝒬, ℛ) − Val_G(𝒜♯, ℬ♯)| ≤ 15ν`.

**Formalization Note** `ψ` is a two-qubit density matrix; both values are on `ψ^{⊗n}`, the first by
formula (22). The expectations are `∑_x p_X(x)(·)` with the marginals (15). -/
theorem lemma_3_5 {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : MIPRE.Game X Y A B) (n : ℕ) (hn : 1 ≤ n)
    (ψ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hψ : QAlgorithms.IsDensityMatrix ψ) (hmm : HasMaxMixedMarginals ψ)
    (Q : X → A → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (R : Y → B → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (ν : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hQ : ∑ x, pX G x * nnorm2 (∑ a, (Q x a)ᴴ * Q x a - 1) ^ 2 ≤ ν ^ 4)
    (hR : ∑ y, pY G y * nnorm2 (∑ b, (R y b)ᴴ * R y b - 1) ^ 2 ≤ ν ^ 4) :
    ∃ (SA : X → MIPRE.POVM A (Fin n → Fin 2)) (SB : Y → MIPRE.POVM B (Fin n → Fin 2)),
      |val G (tensorPow ψ n) (fun x a => (Q x a)ᴴ * Q x a) (fun y b => (R y b)ᴴ * R y b) -
          val G (tensorPow ψ n) (povmMats SA) (povmMats SB)| ≤ 15 * ν := by sorry

end UnitalMIP
