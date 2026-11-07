-- Prove2me | Theorems.Thm_QBFBackdoor_corollary_5_8
-- name    : QBFBackdoor.corollary_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:27.363952+00:00
-- url     : https://prove2.me/theorems/aa339922-01c0-4a1c-8137-6f3f38ba0e6d
-- title:
--   Corollary 5.8 — 4-Disjunct-QBF$(\Gamma_{\mathrm{AFF}})$ is PSPACE-hard
-- statement:
--   Let 4-Disjunct-QBF$(\Gamma_{\mathrm{AFF}})$ be the problem of deciding whether a QBF $Q.(\phi_1\vee\phi_2\vee\phi_3\vee\phi_4)$ with four disjuncts, each a conjunction of atoms $(x)$, $(\neg x)$, $(x=y)$, is true. Then
--
--   $$
--   4\text{-Disjunct-QBF}(\Gamma_{\mathrm{AFF}}) \text{ is PSPACE-hard.}
--   $$
--
--   With a constant number of disjuncts, the reverse reduction of Lemma 4.4 turns this into hardness of QBF with a backdoor of size $\lceil\log_2 4\rceil=2$ (Theorem 5.9).
--
--   Differences from the source:
--   - encoding: PSPACE-hard (standard machine model, instances as strings) → the published OptimalQueuingComplexity.Restless.PSPACEHard (every PSPACE language reduces by a Mathlib TM2 polynomial-time map) on structural injective bit encodings; reason: the standard notions; the encodings are injective and of length polynomial in ∥Φ∥, so no instance changes
--   - reading: 4-Disjunct-QBF(ΓAFF) → instances with exactly four disjuncts; others are no-instances; reason: q-Disjunct-C is defined by ϕ = ϕ1 ∨ … ∨ ϕq (p.16)
--   - encoding: variables x1, …, xn and prefix Q1x1 … Qnxn → variables Fin n quantified in index order, q j = true meaning ∃; reason: relabelling; same formulas
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), Corollary 5.8, p.26

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete
import Definitions.Def_QBFBackdoor_encCNF

namespace QBFBackdoor

open OptimalQueuingComplexity.Restless

/-- **Corollary 5.8.** Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, *Backdoors for Quantified Boolean
Formulas*, arXiv:2604.15927 (held version, sha256 3ea1662e…), p.26: "4-Disjunct-QBF(ΓAFF) is PSPACE-hard."

The language of encoded disjunctive QBFs over `Γ_AFF` with exactly four disjuncts that are true is
PSPACE-hard under polynomial-time many-one reductions.

**Formalization Note** PSPACE-hardness is the published `PSPACEHard` on Mathlib TM2 machines, for
the structural encoding `encDQBF`. Instances with a number of disjuncts other than four are
no-instances. -/
theorem corollary_5_8 :
    PSPACEHard encDQBF (fun I : DQBFInst => I.Φ.disj.length = 4 ∧ I.Φ.holds) := by sorry

end QBFBackdoor
