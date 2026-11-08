-- Prove2me | Theorems.Thm_RoundOptVSS_lemma_5_3
-- name    : RoundOptVSS.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:05:43.5686+00:00
-- url     : https://prove2.me/theorems/7e5d13ee-69df-4134-b800-b1d84e90165f
-- title:
--   Lemma 5.3 — security of packed IC: (P1)–(P5), $\varepsilon_{nr}=1/(|\mathbb F|-1)$, $\varepsilon_{au}=\delta/|\mathcal A|$
-- statement:
--   **Lemma 5.3** (Security of packed IC). For the packed IC of Protocol 3, with the standing assumptions ($h\ge1$, distinct packing nodes, $\beta_1=0$ if $h=1$, $\alpha_0\in\mathcal A$), $\delta=h+t-1$ and $\mathcal A=\mathbb F\setminus\{0,\beta_1,\dots,\beta_h\}$:
--
--   1. **(P1) Correctness.** For all $F,G$ of degree at most $\delta$, every $d\in\mathbb F^\times$ and every $\alpha\in\mathcal A$: the finish on the honest checkpoint $cp=(d,dF+G)$ is $\mathsf{ok}$ and $\mathrm{Open}(\mathrm{val}(F),F,cp,(\alpha,F(\alpha),G(\alpha)))=1$.
--   2. **(P2) Honest failure.** An honest sender's finish is $\mathsf{ok}$ or $\mathsf{fail}(x)$.
--   3. **(P3) Nonrepudiation.** For all $F,G$ of degree at most $\delta$ and every key string $k$ (malformed allowed),
--   $$\Pr_{d\leftarrow\mathbb F^\times}\big[\mathrm{Open}(\mathrm{val}(F),F,(d,dF+G),k)=0\big]\le\frac1{|\mathbb F|-1}.$$
--   4. **(P4) Unforgeability.** For all $F,G$ of degree at most $\delta$, every checkpoint $cp$ and every candidate $(x',P)$,
--   $$\Pr_{\alpha\leftarrow\mathcal A}\big[\mathrm{out}=\mathsf{ok}\wedge x'\ne\mathrm{val}(F)\wedge\mathrm{Open}(x',P,cp,(\alpha,F(\alpha),G(\alpha)))=1\big]\le\frac{\delta}{|\mathcal A|},$$
--   and if $P\ne F$ the same bound holds for $\Pr_\alpha[\mathrm{out}=\mathsf{ok}\wedge\mathrm{Open}(x',P,cp,(\alpha,F(\alpha),G(\alpha)))=1]$.
--   5. **(P5) Privacy.** For every set $V$ of at most $t$ parties, the law of $(cp,\mathrm{out},(\mathrm{key}_w)_{w\in V})$ under honest sender and holder is the same for every two inputs.
--   6. If $t\ge1$, then $\max\{1/(|\mathbb F|-1),\,\delta/|\mathcal A|\}=\delta/|\mathcal A|$.
--
--   This is the authentication primitive of the WSS: (P3) and (P4) give the per-label error $1/(q-1)+\delta/|\mathcal A|$ that enters $\varepsilon_{\rm WSS}$ and display (8).
--
--   **Formalization Note** In (P4) the adversary's checkpoint and candidate are fixed; they are independent of the target point $\alpha_w$, so averaging gives the printed probability and conditioning on the adversary's view and $(F,G)$ gives the conditional clause.
--
--   Differences from the source:
--   - generalization: (P4): Pr over the execution, adversary holding all Distribute messages except key_w and fixing its candidate; conditional clause under conditional uniformity of α_w → for every fixed checkpoint and candidate, Pr over α_w ← 𝒜 alone; reason: the candidate is independent of α_w (resp. α_w is uniform given it); averaging over the conditioning gives both printed forms
--   - encoding: (P3): every key string that is a function of the Distribute messages → every fixed key string in Option (𝔼 × 𝔼 × 𝔼); reason: such a key is fixed before the holder samples d
--   - encoding: (P1) with honest sender and holder: out = ok, x_H = x, Open = 1 for every w → for every valid (F, G), d ∈ 𝔽^×, α ∈ 𝒜 (x = val F); reason: the honest keys have α_w ∈ 𝒜
--   - encoding: polynomials of degree at most δ; uniform F, G with val(F) = x → natDegree ≤ δ; uniform coefficient vectors of length δ + 1; reason: same objects
--   - encoding: ε = max{…} = δ/|𝒜| (t ≥ 1) → the identity in ℝ≥0∞ under 1 ≤ t; reason: same numbers
-- source:
--   Liu-Zhang, Masserova, Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity, manuscript (2026; STOC 2027 submission, sha256 3a45d95d…), Lemma 5.3 (pp.17–18) with Definition 5.2 (P1)–(P5) (p.16), Protocol 3 (p.17)

import Mathlib
import Definitions.Def_RoundOptVSS_PackedIC

open scoped Polynomial ENNReal
open Polynomial Classical

namespace RoundOptVSS

/-- **Lemma 5.3** (Security of packed IC), pp.17–18 of Liu-Zhang, Masserova, *Round-Optimal
Statistical Verifiable Secret Sharing with Polynomial Complexity*, manuscript (STOC 2027
submission, sha256 3a45d95d…), for the packed IC of §5.1 / Protocol 3, with the properties of
Definition 5.2 (p.16):
* (P1) correctness: with honest sender and holder, for every valid `(F, G)`, every challenge
  `d ∈ 𝔽^×` and every point `α ∈ A`, the finish is `ok` and `Open(val F, F, cp, key) = 1`;
* (P2) honest failure: an honest sender's finish is `ok` or `fail(x)`;
* (P3) nonrepudiation with `ε_nr = 1/(|𝔽| − 1)`: for an honest holder with a valid state and
  every key string `k` fixed before its challenge (malformed allowed),
  `Pr_d[Open(x_H, F, (d, dF + G), k) = 0] ≤ 1/(|𝔽| − 1)`;
* (P4) unforgeability with `ε_au = δ/|A|`, per verifier and actual candidate: for an honest
  sender with valid `(F, G)` and every checkpoint and candidate fixed independently of the
  verifier's point `α ← A`, `Pr_α[out = ok ∧ x′ ≠ x ∧ Open(x′, P, cp, key_w) = 1] ≤ δ/|A|`, and
  every candidate `P ≠ F` passes (with `out = ok`) with probability at most `δ/|A|`;
* (P5) privacy: with honest sender and holder, the law of `(cp, out, (key_w)_{w ∈ V})` is the
  same for all inputs, for every `V` of at most `t` parties;
* and `max{1/(|𝔽| − 1), δ/|A|} = δ/|A|` when `t ≥ 1`.

**Formalization Note.** (P4) is stated with the adversary's checkpoint and candidate fixed
(they are independent of `α_w` given everything else); averaging over them gives the printed
probability, and the conditional-uniformity clause is the same bound conditionally on each value
of the adversary's view and `(F, G)`. -/
theorem lemma_5_3 {𝔽 𝔼 : Type} [Field 𝔽] [Fintype 𝔽] [Field 𝔼] [Fintype 𝔼] [Algebra 𝔽 𝔼]
    (I : ICParams 𝔽) (hI : I.Standing) (n : ℕ) :
    (∀ F G : 𝔼[X], F.natDegree ≤ I.δ → G.natDegree ≤ I.δ → ∀ d : 𝔽ˣ, ∀ α ∈ I.A,
      senderFinish I (val I F) F G (holderCheckpoint (d : 𝔽) F G) = .ok ∧
        Accepts I (val I F) F (holderCheckpoint (d : 𝔽) F G) (some (senderKey α F G))) ∧
    (∀ (x : Fin I.h → 𝔼) (F G : 𝔼[X]) (cp : 𝔽 × 𝔼[X]),
      senderFinish I x F G cp = .ok ∨ senderFinish I x F G cp = .fail x) ∧
    (∀ F G : 𝔼[X], F.natDegree ≤ I.δ → G.natDegree ≤ I.δ → ∀ k : Option (ICKey 𝔼),
      (PMF.uniformOfFintype 𝔽ˣ).toOuterMeasure
          {d | ¬ Accepts I (val I F) F (holderCheckpoint (d : 𝔽) F G) k} ≤
        ((Fintype.card 𝔽 : ℝ≥0∞) - 1)⁻¹) ∧
    (∀ F G : 𝔼[X], F.natDegree ≤ I.δ → G.natDegree ≤ I.δ →
      ∀ (cp : 𝔽 × 𝔼[X]) (x' : Fin I.h → 𝔼) (P : 𝔼[X]),
        (PMF.uniformOfFinset I.A ⟨I.α0, hI.α0_mem⟩).toOuterMeasure
            {α | senderFinish I (val I F) F G cp = .ok ∧ x' ≠ val I F ∧
              Accepts I x' P cp (some (senderKey α F G))} ≤ (I.δ : ℝ≥0∞) / I.A.card ∧
        (P ≠ F → (PMF.uniformOfFinset I.A ⟨I.α0, hI.α0_mem⟩).toOuterMeasure
            {α | senderFinish I (val I F) F G cp = .ok ∧
              Accepts I x' P cp (some (senderKey α F G))} ≤ (I.δ : ℝ≥0∞) / I.A.card)) ∧
    (∀ (x₀ x₁ : Fin I.h → 𝔼) (V : Finset (Fin n)), V.card ≤ I.t →
      (icLaw I n x₀).map (fun o => (o.1, o.2.1, fun w : V => o.2.2 w)) =
        (icLaw I n x₁).map (fun o => (o.1, o.2.1, fun w : V => o.2.2 w))) ∧
    (1 ≤ I.t → max ((Fintype.card 𝔽 : ℝ≥0∞) - 1)⁻¹ ((I.δ : ℝ≥0∞) / I.A.card) =
      (I.δ : ℝ≥0∞) / I.A.card) := by sorry

end RoundOptVSS
