-- Prove2me | Theorems.Thm_QStateSearch_val_comparison
-- name    : QStateSearch.val_comparison
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:25:37.94978+00:00
-- url     : https://prove2.me/theorems/fafac340-d20a-4023-9924-5cd7c47b9e6d
-- title:
--   Proof of Theorem 4 — $|\mathrm{val}_{R_\psi}(V)-\mathrm{val}_I(V)|\le\max_P|\mathrm{Acc}_{R_\psi}(V,P)-\mathrm{Acc}_I(V,P)|$
-- statement:
--   For every classical-message verifier $V$ and any two oracles $O,O'$,
--   $$
--   \big|\mathrm{val}_O(V)-\mathrm{val}_{O'}(V)\big|\le\max_P\big|\mathrm{Acc}_O(V,P)-\mathrm{Acc}_{O'}(V,P)\big| ,
--   $$
--   the maximum over deterministic classical provers. The paper states it for $O=R_\psi$, $O'=I$.
--
--   The difference of the optimal values is at most the difference obtained by keeping one optimal prover fixed; with Eq. (3) this gives the second clause of Theorem 4.
--
--   Differences from the source:
--   - generalization: a verifier whose classical messages alternate (p.9) and whose outgoing message registers are measured in the computational basis (p.8) → a `Verifier`: any finite list of unitary steps, controlled queries, verifier messages given by any instrument $\{K_a\}$ with $\sum_a K_a^\dagger K_a=I$, and padded prover messages received through unitaries, in any order; reason: the paper's verifiers are instances (alternation is a convention that padding makes harmless, p.9; measuring a register in the computational basis is $K_a=|a\rangle\langle a|\otimes I$)
--   - encoding: private quantum registers and private measurements; controlled and uncontrolled oracle calls → pure states on $\{0,1\}\times[D]\times W$ for a finite workspace $W$ with private measurements deferred; every call controlled; reason: the paper defers private measurements (p.10) and allows controlled calls (p.8); an uncontrolled call is a controlled one with the control set to $|1\rangle$
--   - generalization: the oracles $R_\psi$ and $I$ → any two $D\times D$ matrices $O,O'$; reason: the paper's case is $O=R_\psi$, $O'=I$
--   - encoding: $\max_P$ → $\sup_P$; reason: the supremum is attained (finitely many relevant replies)
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), proof of Theorem 4, last two paragraphs, pp.13–14

import Mathlib
import Definitions.Def_QStateSearch_Verifier
import Definitions.Def_QStateSearch_AccW
import Definitions.Def_QStateSearch_val

namespace QStateSearch

/-- **Proof of Theorem 4, val comparison.** The difference between the optimal values is at most
the largest difference of acceptance probabilities for one fixed prover:
`|val_O(V) − val_{O'}(V)| ≤ max_P |Acc_O(V, P) − Acc_{O'}(V, P)|`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), proof of Theorem 4, last two paragraphs, pp.13–14 (stated there for `O = R_ψ`, `O' = I`).

**Formalization Note.** Stated for any two oracle matrices `O`, `O'`; the paper's case is
`O = R_ψ`, `O' = I`. `max_P` is `⨆ P`. -/
theorem val_comparison {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] (V : Verifier D W)
    (O O' : Matrix (Fin D) (Fin D) ℂ) :
    |val V O - val V O'| ≤ ⨆ P : Prover, |AccW V O P - AccW V O' P| := by sorry

end QStateSearch
