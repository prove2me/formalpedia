-- Prove2me | Theorems.Thm_QPACLarge_eq_4_5
-- name    : QPACLarge.eq_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:10:57.889354+00:00
-- url     : https://prove2.me/theorems/d80e4d96-fc79-4cc8-be91-9e75a9d6499c
-- title:
--   Eqs. (4)–(5) — $W$ is an isometry, $W|\psi_F\rangle=(2M)^{-1/2}\sum_a(1+Z_a)|a\rangle$, and $P_F(a)=(1+Z_a)^2/(2M)$
-- statement:
--   Let $n \ge 1$, $N = 2^n$, $M = 2^r$, $f : \{0,1\}^n \to \{0,1\}$ with $F = (-1)^f$, and $W|\ell\rangle = H^{\otimes r}|J(\ell)\rangle$. Then
--
--   1. $W$ is an isometry: $\langle Wv, Ww\rangle = \langle v, w\rangle$ for all vectors $v, w$ of the label space;
--   2. (Eq. (4)) $W|\bot\rangle = \frac{1}{\sqrt M}\sum_{a} |a\rangle$ and $W|x\rangle_{\mathrm{idx}} = \frac{1}{\sqrt M}\sum_a H_a(x)|a\rangle$;
--   3. (Step 3) $W|\psi_F\rangle = \frac{1}{\sqrt{2M}} \sum_{a} (1 + Z_a)|a\rangle$;
--   4. (Eq. (5)) measuring the seed register gives $a$ with probability $|\langle a|W|\psi_F\rangle|^2 = P_F(a) = \frac{(1+Z_a)^2}{2M}$.
--
--   The reference branch $|\bot\rangle$ contributes the constant amplitude $1$, so the measured seed is biased toward positive correlation $Z_a$; this is the correlation-biased quantum sampler.
--
--   **Formalization Note** Labels are abstract (`Option (Qubits n)`); $|\ell\rangle$ is the indicator vector of $\ell$, and inner products are $\sum \overline{v}\,w$.
--
--   Differences from the source:
--   - encoding: the $(n+1)$-qubit index register with $|\bot\rangle = |0\rangle|0^n\rangle$, $|x\rangle = |1\rangle|x\rangle$ → vectors indexed by the abstract labels $\{\bot\} \cup \{0,1\}^n$; reason: $W$ is defined on the span of these $N+1$ basis states only
--   - encoding: the probability of observing a basis state is the squared absolute value of its amplitude → $\|(W\psi_F)(a)\|^2 = P_F(a)$; reason: the Born rule for a computational-basis measurement
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 3.2.1, Eq. (4), p.23; Section 3.2.2, Steps 3–4, pp.24–25, Eq. (5)

import Mathlib
import Definitions.Def_QPACLarge_Wmap
import Definitions.Def_QPACLarge_psiF
import Definitions.Def_QPACLarge_PF

namespace QPACLarge

open QAlgorithms

/-- **Eqs. (4)–(5): `W` is an isometry, `W|ψ_F⟩ = (2M)^{−1/2} Σₐ (1 + Z_a)|a⟩`, and `P_F`.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 3.2.1, p.23: "`W|⊥⟩ = (1/√M) Σ_{a∈A} |a⟩`, `W|x⟩_idx = (1/√M) Σ_{a∈A} H_a(x)|a⟩`. (4)
Since `J` is injective and the Hadamard transform is unitary, it is not hard to check that `W` is an
isometry." Section 3.2.2, Steps 3–4, pp.24–25: "Apply the isometry `W`. By Equation (4) and
linearity, `W|ψ_F⟩ = … = (1/√(2M)) Σ_{a∈A} (1 + Z_a)|a⟩`." "Measure the seed register. The
probability of observing a basis state is the squared absolute value of its amplitude, so the
resulting seed is distributed according to `P_F(a) ≜ (1 + Z_a)²/(2M)`. (5)"

**Formalization Note.** `M = |A|` is `Fintype.card (Seed n)`; `H_a(x) = (−1)^{q_a(x)}` is
`sgn (qa a x)`; the target enters as `f` with `F = (−1)^f`. Isometry is preservation of the inner
product `⟨v, w⟩ = Σ conj(v) w`. `|ℓ⟩` is the indicator vector of the label `ℓ`. -/
theorem eq_4_5 (n : ℕ) (hn : 1 ≤ n) (f : Qubits n → Bool) :
    (∀ v w : Option (Qubits n) → ℂ,
      ∑ a : Seed n, star (Wmap v a) * Wmap w a = ∑ ℓ, star (v ℓ) * w ℓ) ∧
    (∀ a : Seed n, Wmap (fun ℓ => if ℓ = none then 1 else 0) a =
      ((Real.sqrt (Fintype.card (Seed n)))⁻¹ : ℝ)) ∧
    (∀ (x : Qubits n) (a : Seed n), Wmap (fun ℓ => if ℓ = some x then 1 else 0) a =
      ((Real.sqrt (Fintype.card (Seed n)))⁻¹ * sgn (qa a x) : ℝ)) ∧
    (∀ a : Seed n, Wmap (psiF f) a =
      ((Real.sqrt (2 * Fintype.card (Seed n)))⁻¹ * (1 + Zcorr f a) : ℝ)) ∧
    (∀ a : Seed n, ‖Wmap (psiF f) a‖ ^ 2 = PF f a) := by sorry

end QPACLarge
