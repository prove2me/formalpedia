-- Prove2me | Theorems.Thm_QuantumAdviceAmplification_Separation_lemma_3_3
-- name    : QuantumAdviceAmplification.Separation.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:04:53.374199+00:00
-- url     : https://prove2.me/theorems/6e4f02ed-4072-4e2e-87ec-7cf025773975
-- title:
--   Lemma 3.3 — Second-moment syndrome covering
-- statement:
--   Let $0\le r\le\ell$. Draw the Toeplitz seed $t\in\mathbb F_2^{\ell-1}$ and syndrome $s\in\mathbb F_2^q$ independently and uniformly. For the Hamming ball $\mathcal B(\ell,r)$ of volume $V(\ell,r)$,
--   $$\Pr_{t,s}[\forall w\in\mathcal B(\ell,r):H_{T(t)}w\ne s]\le\frac{2^q}{V(\ell,r)}.$$
--   This bounds the chance that the ball misses a random syndrome.
--
--   Differences from the source:
--   - encoding: F2 vectors with one-based coordinates, ell>=2 and 1<=d<=ell-1 → Bool coordinates with ZMod 2 arithmetic, zero-based Fin indices, and positive d,q with ell=q+d; reason: the Boolean/field and coordinate bijections preserve the source code and all parameter choices
--   - encoding: probabilities and expectations over independent uniform finite choices → normalized finite sums and a uniform PMF on the product seed space; reason: the product law is exactly independent uniform sampling; every index space used here is nonempty
-- source:
--   Shih-Han Hung, Han-Hsuan Lin, STOC 2027 submission #1297 (October 2026), p.8, Lemma 3.3

import Definitions.Def_QuantumAdviceAmplification_Separation_parameters
set_option autoImplicit false
open Classical

namespace QuantumAdviceAmplification.Separation

theorem lemma_3_3 (S : BlockShape) (r : ℕ) (hr : r ≤ S.ell) :
    uniformMean (fun ts : Bits (S.ell - 1) × (Fin S.q → ZMod 2) =>
      if ∀ w : Bits S.ell, weight w ≤ r → syndrome S ts.1 w ≠ ts.2 then 1 else 0) ≤
      (2 : ℝ) ^ S.q / volume S.ell r := by sorry

end QuantumAdviceAmplification.Separation
