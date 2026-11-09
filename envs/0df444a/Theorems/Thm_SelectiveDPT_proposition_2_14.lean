-- Prove2me | Theorems.Thm_SelectiveDPT_proposition_2_14
-- name    : SelectiveDPT.proposition_2_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:53:26.905472+00:00
-- url     : https://prove2.me/theorems/3373c431-0526-4a0b-a4d2-9e4c04dbba3a
-- title:
--   Proposition 2.14 [JZ26] — relational multiplicative adversary bound $Q^{\mathcal D}_\varepsilon(R) \ge \log_c(1+(\lambda-1)(\sqrt{1-\varepsilon}-\sqrt\eta)^2)$
-- statement:
--   Let $R \subseteq D \times Y$ be a relation on a domain $D \subseteq X^\iota$ over a finite index set $\iota$, and let $\mu$ be a distribution on $D$. Let $(\Gamma, \lambda, \eta)$ be a valid witness: $\Gamma$ positive definite with smallest eigenvalue $1$ and $\Gamma|\mathcal D\rangle = |\mathcal D\rangle$, $\lambda \in (1, \|\Gamma\|]$, $\eta > 0$ and $\|\Pi_{R^{-1}(y)}\Pi_{\Gamma,\le\lambda}\|^2 \le \eta$ for all $y \in Y$. Let $c = \max_{i,p}\|O_{i,p}^\dagger\Gamma^{1/2}O_{i,p}\Gamma^{-1/2}\|^2$. Then for every $\varepsilon < 1-\eta$,
--   $$Q^{\mathcal D}_\varepsilon(R) \;\ge\; \log_c\!\Big(1 + (\lambda-1)\big(\sqrt{1-\varepsilon}-\sqrt\eta\big)^2\Big).$$
--
--   The paper attributes this bound to Jeffery and Zur and derives it from Proposition 2.12 (Špalek's initial conditions with the terminal value of Ambainis, Magnin, Roetteler and Roland); it does not prove it. Theorem 4.7 applies it to the selective direct product on $m$ copies.
--
--   **Formalization Note** The bound is compared in $[0,\infty]$; a negative logarithm counts as $0$.
--
--   Differences from the source:
--   - generalization: D ⊆ X^n → D ⊆ X^ι for any finite index type ι; reason: X^n is the case ι = Fin n; Theorem 4.7 applies the bound to X^{mn} indexed by Fin m × Fin n
--   - encoding: c = max_{i,p,ρ} Tr[ΓO†ρO]/Tr[Γρ] = max_{i,p}‖O†Γ^{1/2}OΓ^{−1/2}‖² → c defined by the norm form; reason: the two forms agree (Remark 2.13, a milestone)
--   - encoding: inputs x ∈ X^n with |X| = d, a T-query algorithm measuring its work register and post-processing the result → X = ZMod d, inputs Fin n → ZMod d with a Finset domain D, QAlgorithms.QueryAlg with workspace Fin b for any b, a full computational-basis measurement followed by an output map, query complexity in ℕ∞ (⊤ if no algorithm exists) compared in [0, ∞]; reason: relabelling X as Z_d is the paper's own convention (p.9); only the workspace dimension matters; measuring a designated output register is a special output map
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Proposition 2.14, p.17

import Mathlib
import Definitions.Def_SelectiveDPT_Qdist
import Definitions.Def_SelectiveDPT_IsMultAdvWitness
import Definitions.Def_SelectiveDPT_rate

open scoped ENNReal

namespace SelectiveDPT

/-- Proposition 2.14 (Multiplicative Adversary Bound) of arXiv:2609.26678
(Beame–Kornerup–Whitmeyer), p.17, attributed to Jeffery–Zur [JZ26] and derived there from
Proposition 2.12; the paper does not prove it. Let `R ⊆ D × Y` be a relation and `D` a
distribution over `D ⊆ X^n`. Let `Γ` be a `|D| × |D|` positive-definite matrix with smallest
eigenvalue `1` such that `Γ|D⟩ = |D⟩`. Let `λ ∈ (1, ‖Γ‖]` and `η > 0` satisfy
`‖Π_{R⁻¹(y)} Π_{Γ,≤λ}‖² ≤ η` for all `y ∈ Y`. Then for
`c = max_{i,p} ‖O†_{i,p} Γ^{1/2} O_{i,p} Γ^{−1/2}‖²` and `ε < 1 − η`,
`Q^D_ε(R) ≥ log_c(1 + (λ − 1)(√(1 − ε) − √η)²)`.

**Formalization Note.** Stated for inputs indexed by an arbitrary finite type `ι` (the paper's
`X^n` is `ι = Fin n`); Theorem 4.7 applies it to `m` copies with `ι = Fin m × Fin n`. The bound is
in `[0, ∞]` (a negative value of `log_c` is `0`); `Q^D_ε` is `⊤` when no algorithm succeeds. -/
theorem proposition_2_14 {ι Y : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} [NeZero d]
    (D : Finset (ι → ZMod d)) (R : (ι → ZMod d) → Y → Prop) (μ : (ι → ZMod d) → ℝ)
    (hμ : IsDistOn μ D) (Γ : Matrix D D ℂ) (lam η ε : ℝ)
    (hΓ : IsMultAdvWitness μ D R Γ lam η) (hε : ε < 1 - η) :
    ENNReal.ofReal (Real.logb (rate D Γ) (1 + (lam - 1) * (Real.sqrt (1 - ε) - Real.sqrt η) ^ 2)) ≤
      (Qdist D μ R ε : ℝ≥0∞) := by sorry

end SelectiveDPT
