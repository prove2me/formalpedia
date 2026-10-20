-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_instrument_linkAction
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.instrument_linkAction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:39:14.006823+00:00
-- url     : https://prove2.me/theorems/79dd59f0-0edd-42e8-939d-182ca7070648
-- title:
--   §IV D: action of generalized instruments
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $\{S_i\}$ be an $(n+1)$-instrument, $n\ge1$, and let $R$ be a probabilistic $n$-comb on its inner-slot signature. The action is the link contraction on the inner wires. Each resulting operator is a quantum-operation Choi operator:
--
--   $$
--   Q_i=S_i*R,\qquad Q_i\succeq0,\quad Q_i\preceq C_i\text{ for some channel Choi operator }C_i.
--   $$
--
--   The physical input convention is a normalized or subnormalized comb, not an arbitrarily scaled CP operator. The one-instrument base has no physical zero-order comb to insert.
--
--   For a deterministic input comb, the sum of these output operations is a channel.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 16, §IV D: action of generalized instruments

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF pp.16–17, Eq.(64): each contracted instrument branch is a quantum operation.
The linked operator is computed by slotAction, not supplied as a free variable. -/
theorem instrument_linkAction (s : Signature) (n k : ℕ) (hn : 0 < n)
    (P : Fin k → Matrix (Basis s (n+1)) (Basis s (n+1)) ℂ)
    (hP : CombInstrument s (n+1) k P)
    (R : Matrix (Basis (slots s) n) (Basis (slots s) n) ℂ)
    (hR : Probabilistic (slots s) n R) :
    (∀ i, OperationChoi (slotAction s n (P i) R)) ∧
      (Deterministic n (slots s) R →
        ChannelChoi (∑ i, slotAction s n (P i) R)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
