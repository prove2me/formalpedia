-- Prove2me | Theorems.Thm_PPSLattice_theorem_4_5
-- name    : PPSLattice.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:37:31.455043+00:00
-- url     : https://prove2.me/theorems/1894e604-82f8-447b-b200-a19a1f4dfed4
-- title:
--   Theorem 4.5 — one-way functions give blind garbled circuits with $|\mathrm{gk}|=\ell(2\lambda+1)$, $|\tilde x|=\ell(\lambda+1)$
-- statement:
--   Assume one-way functions exist. Then there is a garbling scheme, with polynomial-time algorithms, that is a blind garbled circuit scheme (Definition 4.4) for all $s,\ell\ge1$, and such that every $\mathrm{gk}$ output by $\mathrm{Setup}(1^\lambda,1^s,1^\ell)$ and every garbled input $\tilde x=\mathrm{InpGarb}(\mathrm{gk},x)$, $x\in\{0,1\}^\ell$, satisfy
--   $$|\mathrm{gk}|=\ell(2\lambda+1),\qquad |\tilde x|=\ell(\lambda+1).$$
--
--   The garbling key is part of $\mathrm{msk}$ and the garbled digest $\tilde{\mathbf A}_S$ is part of $\mathrm{sk}_S$, so these sizes enter the compactness analysis of §4.4.
--
--   Differences from the source:
--   - reading: one-way functions (not defined in the paper) → OWFExists: a polynomial-time f that every uniform PPT inverter inverts on f(x), x ← {0,1}^n, with negligible probability; reason: standard definition, in the machine model of every other adversary of the mission
--   - reading: for any positive polynomial s, ℓ → one scheme whose Setup receives s, ℓ ≥ 1 in unary; reason: covers every pair of positive polynomials
--   - reading: blindness with gk ← Setup(1^λ, 1^s, 1^ℓ) → blindness for every gk in the support of Setup; reason: proof of Lemma 4.22, p.29: 'As blindness holds for every garb.gk and every input A_S'
--   - reading: L, the length of the garbled circuit of C → a function glen(λ, s, ℓ, ℓ_out); CircGarb outputs strings of exactly that length; reason: Construction 4.6 uses L_C̃ in MSKGen before any circuit exists
--   - reading: polynomial-time algorithms → Garb.Efficient (exact PPT samplers, polynomial-time InpGarb and Eval); reason: §4.2, p.19
--   - reading: stateful (admissible) PPT adversary → uniform reactive machine RestrictedDec.Adversary (polynomial-time step function, polynomially many coins, bounded state, moves and activations); inadmissible runs scored as a uniform guess; reason: Definitions 4.1, 4.2, 4.4 say PPT adversary; the ½-convention is equivalent to admissibility because an adversary can test its own admissibility
--   - encoding: crs, keys, ciphertexts, messages, set descriptions; [N]; Z_q → bit strings Str (pairs via tup, numbers in binary, least significant bit first); [N] = Finset.Icc 1 N; Z_q = ZMod q; reason: Lean convention; same instances
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Theorem 4.5 ([BLSV18, WW24]), p.20

import Mathlib
import Definitions.Def_PPSLattice_OWFExists
import Definitions.Def_PPSLattice_Garb_Efficient
import Definitions.Def_PPSLattice_Garb_IsBlindGarb
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- **Theorem 4.5** ([BLSV18, WW24]). If one-way functions exist, there is a blind garbled circuit scheme,
for all `s, ℓ ≥ 1`, with `|gk| = ℓ(2λ + 1)` for every `gk` output by `Setup(1^λ, 1^s, 1^ℓ)` and `|x̃| = ℓ(λ + 1)`
for every garbled input `x̃ = InpGarb(gk, x)`, `x ∈ {0,1}^ℓ`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Theorem 4.5, p.20 ("Assuming the existence of one-way functions, there exists a blind garbled circuit
scheme for any positive polynomial s, ℓ with |gk| = ℓ(2λ + 1), |x̃| = ℓ(λ + 1)").

**Formalization Note.** `λ` ranges over the positive integers (§3, p.15: "We denote … the set of positive integers by N"). `s` and `ℓ` are inputs of Setup (in unary), so one scheme serves all positive
polynomials `s, ℓ`. The two lengths are exact, as printed. -/
theorem theorem_4_5 (hOWF : OWFExists) :
    ∃ G : Garb, G.Efficient ∧ G.IsBlindGarb ∧ ∀ lam s ell : ℕ, 1 ≤ lam → 1 ≤ s → 1 ≤ ell →
      ∀ gk ∈ (G.setup lam s ell).support, gk.length = ell * (2 * lam + 1) ∧
        ∀ x : Str, x.length = ell → (G.inpGarb gk x).length = ell * (lam + 1) := by sorry

end PPSLattice
