-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P11_nonunital_not_repeatable
-- name    : QAlgorithms.Papers.Independent.Dependency50.P11.nonunital_not_repeatable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:34:53.442982+00:00
-- url     : https://prove2.me/theorems/1e50a871-6ce9-4a2e-9bf2-14cba2a8f741
-- title:
--   Nonunital channels have no finite repeatable implementation
-- statement:
--   Let $d\ge1$ and let $\mathcal E$ be a completely positive, trace-preserving linear map on operators on $\mathbb C^d$. If $\mathcal E(I_d)\ne I_d$, then
--
--   $$\nexists\,(m,\xi,U)\ \text{implementing }\mathcal E\text{ on every individual use for all horizons},\qquad 1\le m<\infty.$$
--
--   Here $\xi$ is a fixed density matrix of the memory and $U$ is one fixed unitary on memory tensored with the input system; each fresh input is initially independent of the memory and of the other inputs. The same device must work for every product-input history, with no resets or extra environments.
--
--   The obstruction concerns a fixed finite memory serving all horizons, and permits a separate finite device for each finite horizon.
-- source:
--   Repeatable quantum memory channels, arXiv:0808.3851v1, PDF p. 4, Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P11

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

/-- Theorem 2, PDF p.4: nonunital channels have no all-horizon finite-memory implementation. -/
theorem nonunital_not_repeatable {d : ℕ} (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) (hNU : ¬ IsUnital E) :
    ¬ HasFiniteRepeatableImplementation E := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P11

end
