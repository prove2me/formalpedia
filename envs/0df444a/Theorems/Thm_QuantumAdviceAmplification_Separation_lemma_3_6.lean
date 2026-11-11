-- Prove2me | Theorems.Thm_QuantumAdviceAmplification_Separation_lemma_3_6
-- name    : QuantumAdviceAmplification.Separation.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:05:00.775939+00:00
-- url     : https://prove2.me/theorems/872e3492-a599-4588-92d8-b877b4352054
-- title:
--   Lemma 3.6 — Shared-header symmetrization
-- statement:
--   Fix Protocol 1 parameters $\ell\ge2$, $1\le d\le\ell-1$, and $B\ge1$. The Toeplitz seed, cyclic shift, and mask are drawn once and shared by all blocks. Every message $z\in\mathbb F_2^{B\ell}$ and query $a\in[B\ell]$ satisfy
--   $$\Pr[\operatorname{Dec}(a,\operatorname{Enc}(z))\ne z_a]=\mathbb E_tD(C_{T(t)})=\varepsilon^*(\ell,d).$$
--   Thus Protocol 1 is a $B\ell$-to-$m'$ random access code with this error, independent of $B$.
--
--   Differences from the source:
--   - encoding: F2 vectors with one-based coordinates, ell>=2 and 1<=d<=ell-1 → Bool coordinates with ZMod 2 arithmetic, zero-based Fin indices, and positive d,q with ell=q+d; reason: the Boolean/field and coordinate bijections preserve the source code and all parameter choices
--   - encoding: probabilities and expectations over independent uniform finite choices → normalized finite sums and a uniform PMF on the product seed space; reason: the product law is exactly independent uniform sampling; every index space used here is nonempty
--   - encoding: cyclic p minus tau in one-based modular notation → (i+ell-tau)%ell on zero-based indices; reason: tau<ell makes the natural subtraction nonnegative; the expression equals integer modular subtraction
-- source:
--   Shih-Han Hung, Han-Hsuan Lin, STOC 2027 submission #1297 (October 2026), p.10, Lemma 3.6

import Definitions.Def_QuantumAdviceAmplification_Separation_parameters
set_option autoImplicit false
open Classical

namespace QuantumAdviceAmplification.Separation

theorem lemma_3_6 (S : BlockShape) (B : ℕ) (hB : 0 < B) :
    (∀ (z : Bits (B * S.ell)) (a : Fin (B * S.ell)),
      codeError (protocolCode S B) z a = epsilonStar S) ∧
    IsRAC (protocolCode S B) (epsilonStar S) := by sorry

end QuantumAdviceAmplification.Separation
