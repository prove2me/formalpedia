-- Prove2me | Theorems.Thm_QThermalClassical_Supplement_theorem_35_power_law
-- name    : QThermalClassical.Supplement.theorem_35_power_law
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:42:53.674111+00:00
-- url     : https://prove2.me/theorems/c59703c1-83e2-41a2-96f5-6cf49efe844a
-- title:
--   Theorem 35, power-law bullet — for $\alpha\le D$ the power-law Hamiltonian is entangled at every fixed $\beta>0$ for large $L$; its local strength is bounded iff $\alpha>D$
-- statement:
--   Fix a dimension $D\ge1$ and set $m=2$, $a=0$, $J_{x,x}=0$ and $J_{x,y}=1/(1+\|x-y\|_2)^\alpha$ for $x\neq y$ in the Hamiltonian (408) on $\Lambda_L=\{1,\dots,L\}^D$. Then:
--
--   1. for every fixed $\beta>0$ and every real $\alpha\le D$, the Gibbs state is entangled for all sufficiently large $L$;
--   2. for $\alpha>D$ the local interaction strength $\max_q\sum_{P:\ q\in\mathrm{supp}\,P}|c_P|$ is bounded uniformly in $L$;
--   3. for $\alpha\le D$ the local interaction strength tends to $+\infty$ as $L\to\infty$.
--
--   Together with Theorem 1(a) this locates the power-law threshold at $\alpha=D$: separable at some constant temperature for $\alpha>D$, entangled at every temperature independent of system size for $\alpha\le D$.
--
--   Differences from the source:
--   - reading: the local interaction strength remains uniformly bounded in $L$ when $\alpha>D$ and diverges when $\alpha\le D$ → $\max_q\sum_{P\ni q}|c_P|$: $\exists C\ \forall L\ \forall q$, $\le C$ for $\alpha>D$; tends to $+\infty$ as $L\to\infty$ for $\alpha\le D$; reason: the on-site strength of Definition 2.3; 'diverges' as a limit in $L$
--   - encoding: lattice $\{1,\dots,L\}^D$; $\alpha$; sufficiently large $L$ → $D\ge1$, coordinates $0,\dots,L-1$; $\alpha\in\mathbb R$; $\exists L_0\ \forall L\ge L_0$; reason: shifting coordinates leaves differences unchanged; the empty lattice $L=0$ gives the value $0$ for the maximum, irrelevant to the limit
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 35, power-law bullet, p.84

import Mathlib
import Definitions.Def_QThermalClassical_ham
import Definitions.Def_QThermalClassical_gibbs
import Definitions.Def_QThermalClassical_IsSeparable
import Definitions.Def_QThermalClassical_ent35Coeff
import Definitions.Def_QThermalClassical_Supplement_powerLawJ

set_option autoImplicit false

namespace QThermalClassical.Supplement

open Classical in
/-- **Theorem 35, power-law bullet.** For every dimension `D ≥ 1`, setting `m = 2`, `a = 0`,
`J_{x,x} = 0` and `J_{x,y} = 1/(1 + ‖x − y‖₂)^α` for `x ≠ y` in (408):
1. for every fixed `β > 0` and `α ≤ D`, the Gibbs state is entangled for all sufficiently
   large `L`;
2. the local interaction strength `max_q Σ_{P : q ∈ supp P} |c_P|` stays bounded uniformly in `L`
   when `α > D`;
3. it diverges (tends to `+∞` as `L → ∞`) when `α ≤ D`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 35, power-law bullet, p.84.

**Formalization Note.** The Hamiltonian is the published `ent35Coeff D L 2 0 J` with
`J = powerLawJ D L α`; `α` is any real number. "Sufficiently large `L`" is `∃ L₀, ∀ L ≥ L₀`
(`L₀` may depend on `β` and `α`). The maximum over qubits is the real `⨆` over the finite
qubit set (the value `0` for the empty lattice `L = 0`). -/
theorem theorem_35_power_law (D : ℕ) (hD : 1 ≤ D) :
    (∀ β : ℝ, 0 < β → ∀ α : ℝ, α ≤ (D : ℝ) → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ¬ IsSeparable (gibbs (ham (ent35Coeff D L 2 0 (powerLawJ D L α))) β)) ∧
    (∀ α : ℝ, (D : ℝ) < α → ∃ C : ℝ, ∀ (L : ℕ) (q : Ent35Qubit D L 2),
      ∑ P ∈ Finset.univ.filter (fun P : PauliWord (Ent35Qubit D L 2) => q ∈ pauliSupport P),
        |ent35Coeff D L 2 0 (powerLawJ D L α) P| ≤ C) ∧
    (∀ α : ℝ, α ≤ (D : ℝ) → Filter.Tendsto (fun L : ℕ => ⨆ q : Ent35Qubit D L 2,
      ∑ P ∈ Finset.univ.filter (fun P : PauliWord (Ent35Qubit D L 2) => q ∈ pauliSupport P),
        |ent35Coeff D L 2 0 (powerLawJ D L α) P|) Filter.atTop Filter.atTop) := by sorry

end QThermalClassical.Supplement
